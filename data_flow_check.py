#!/usr/bin/env python3
"""
Dynamic data-flow coverage checker for one C function.

The checker computes static def-use obligations with a reaching-definitions
analysis, instruments the function, runs the provided cases, and reports the
missing obligations for:

  - all-defs
  - all-c-uses
  - all-p-uses
  - all-p-uses/some-c-uses
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pycparser import c_ast, c_generator

from coverage_check import (
    PARSER_PREFIX_LINES,
    ParameterInfo,
    function_name,
    function_parameters,
    load_cases,
    normalize_type_name,
    parse_c_file,
    source_excerpt,
    value_to_c_literal,
)


@dataclass(frozen=True)
class VariableInfo:
    id: int
    name: str
    type_name: str
    line: int
    kind: str


@dataclass(frozen=True)
class DefInfo:
    id: int
    var_id: int
    var_name: str
    line: int
    description: str


@dataclass(frozen=True)
class UseInfo:
    id: int
    var_id: int
    var_name: str
    line: int
    kind: str
    expression: str
    decision_id: int | None = None


@dataclass(frozen=True)
class DecisionInfo:
    id: int
    line: int
    expression: str


@dataclass(frozen=True)
class EventInfo:
    id: int
    kind: str
    line: int
    var_id: int | None = None
    def_id: int | None = None
    c_use_id: int | None = None
    p_use_id: int | None = None
    description: str = ""


@dataclass
class StaticObligations:
    c_uses: set[tuple[int, int]]
    p_uses: set[tuple[int, int, int]]
    defs_with_no_reachable_use: set[int]

    def_has_obligation: dict[int, bool]
    c_uses_by_def: dict[int, set[int]]
    p_uses_by_def: dict[int, set[tuple[int, int]]]


@dataclass
class RuntimeData:
    c_uses: set[tuple[int, int]]
    p_uses: set[tuple[int, int, int]]
    c_case: dict[tuple[int, int], int]
    p_case: dict[tuple[int, int, int], int]


class VariableCollector(c_ast.NodeVisitor):
    def __init__(self, line_offset: int) -> None:
        self.line_offset = line_offset
        self.generator = c_generator.CGenerator()
        self.variables: list[VariableInfo] = []
        self.by_name: dict[str, VariableInfo] = {}

    def add_parameter(self, parameter: ParameterInfo, line: int) -> None:
        self._add(parameter.name, parameter.type_name, line, "parameter")

    def visit_Decl(self, node: c_ast.Decl) -> None:
        if node.name:
            type_name = normalize_type_name(self.generator._generate_type(node.type, emit_declname=False))
            if is_supported_primitive_type(type_name):
                self._add(node.name, type_name, self._source_line(node), "local")
        if node.init is not None:
            self.visit(node.init)

    def _source_line(self, node: c_ast.Node | None) -> int:
        coord = getattr(node, "coord", None)
        if coord is None or coord.line is None:
            return 0
        return max(0, coord.line - self.line_offset)

    def _add(self, name: str, type_name: str, line: int, kind: str) -> None:
        if name in self.by_name:
            return
        info = VariableInfo(
            id=len(self.variables),
            name=name,
            type_name=type_name,
            line=line,
            kind=kind,
        )
        self.variables.append(info)
        self.by_name[name] = info


def is_supported_primitive_type(type_name: str) -> bool:
    normalized = normalize_type_name(type_name)
    return "*" not in normalized and "[" not in normalized and "]" not in normalized


def format_use_expression(variable_name: str, context: str | None) -> str:
    if not context or context == variable_name:
        return variable_name
    return f"{variable_name} in {context}"


class DataFlowAnalyzer:
    def __init__(self, function: c_ast.FuncDef, parameters: list[ParameterInfo], line_offset: int) -> None:
        self.function = function
        self.parameters = parameters
        self.line_offset = line_offset
        self.generator = c_generator.CGenerator()

        collector = VariableCollector(line_offset)
        param_nodes = list(function.decl.type.args.params) if function.decl.type.args else []
        for parameter, param_node in zip(parameters, param_nodes):
            collector.add_parameter(parameter, self._source_line(param_node) or self._source_line(function))
        collector.visit(function.body)

        self.variables = collector.variables
        self.variable_by_name = collector.by_name

        self.defs: list[DefInfo] = []
        self.c_uses: list[UseInfo] = []
        self.p_uses: list[UseInfo] = []
        self.decisions: list[DecisionInfo] = []
        self.events: list[EventInfo] = []
        self.edges: dict[int, set[int]] = defaultdict(set)

        self.start_event = self._new_event("start", self._source_line(function), description="function entry")
        self.parameter_defs: list[DefInfo] = []
        self.def_by_decl_node: dict[int, DefInfo] = {}
        self.def_by_assignment_node: dict[int, DefInfo] = {}
        self.def_by_unary_node: dict[int, DefInfo] = {}
        self.use_by_id_node: dict[int, UseInfo] = {}
        self.compound_lvalue_use_by_assignment_node: dict[int, UseInfo] = {}
        self.unary_use_by_node: dict[int, UseInfo] = {}
        self.decision_by_node: dict[int, DecisionInfo] = {}

    def analyze(self) -> StaticObligations:
        exits = [self.start_event]
        for parameter in self.parameters:
            variable = self.variable_by_name.get(parameter.name)
            if variable is None:
                continue
            definition, event_id = self._new_def(
                variable=variable,
                line=variable.line,
                description=f"parameter `{parameter.name}`",
                node=None,
            )
            self.parameter_defs.append(definition)
            exits = self._append_events(exits, [event_id])

        self._build_statement(self.function.body, exits)
        return self._compute_static_obligations()

    def _source_line(self, node: c_ast.Node | None) -> int:
        coord = getattr(node, "coord", None)
        if coord is None or coord.line is None:
            return 0
        return max(0, coord.line - self.line_offset)

    def _new_event(
        self,
        kind: str,
        line: int,
        *,
        var_id: int | None = None,
        def_id: int | None = None,
        c_use_id: int | None = None,
        p_use_id: int | None = None,
        description: str = "",
    ) -> int:
        event = EventInfo(
            id=len(self.events),
            kind=kind,
            line=line,
            var_id=var_id,
            def_id=def_id,
            c_use_id=c_use_id,
            p_use_id=p_use_id,
            description=description,
        )
        self.events.append(event)
        return event.id

    def _new_point(self, line: int, description: str) -> int:
        return self._new_event("point", line, description=description)

    def _new_def(
        self,
        variable: VariableInfo,
        line: int,
        description: str,
        node: c_ast.Node | None,
    ) -> tuple[DefInfo, int]:
        definition = DefInfo(
            id=len(self.defs),
            var_id=variable.id,
            var_name=variable.name,
            line=line,
            description=description,
        )
        self.defs.append(definition)
        if isinstance(node, c_ast.Decl):
            self.def_by_decl_node[id(node)] = definition
        elif isinstance(node, c_ast.Assignment):
            self.def_by_assignment_node[id(node)] = definition
        elif isinstance(node, c_ast.UnaryOp):
            self.def_by_unary_node[id(node)] = definition
        event_id = self._new_event(
            "def",
            line,
            var_id=variable.id,
            def_id=definition.id,
            description=description,
        )
        return definition, event_id

    def _new_c_use(
        self,
        variable: VariableInfo,
        line: int,
        expression: str,
        node: c_ast.Node | None,
    ) -> tuple[UseInfo, int]:
        use = UseInfo(
            id=len(self.c_uses),
            var_id=variable.id,
            var_name=variable.name,
            line=line,
            kind="c-use",
            expression=expression,
        )
        self.c_uses.append(use)
        if isinstance(node, c_ast.ID):
            self.use_by_id_node[id(node)] = use
        event_id = self._new_event(
            "c-use",
            line,
            var_id=variable.id,
            c_use_id=use.id,
            description=expression,
        )
        return use, event_id

    def _new_p_use(
        self,
        variable: VariableInfo,
        line: int,
        expression: str,
        decision_id: int,
        node: c_ast.Node | None,
    ) -> tuple[UseInfo, int]:
        use = UseInfo(
            id=len(self.p_uses),
            var_id=variable.id,
            var_name=variable.name,
            line=line,
            kind="p-use",
            expression=expression,
            decision_id=decision_id,
        )
        self.p_uses.append(use)
        if isinstance(node, c_ast.ID):
            self.use_by_id_node[id(node)] = use
        event_id = self._new_event(
            "p-use",
            line,
            var_id=variable.id,
            p_use_id=use.id,
            description=expression,
        )
        return use, event_id

    def _new_decision(self, node: c_ast.Node, expression: c_ast.Node | None) -> DecisionInfo:
        if id(node) in self.decision_by_node:
            return self.decision_by_node[id(node)]
        decision = DecisionInfo(
            id=len(self.decisions),
            line=self._source_line(node) or self._source_line(expression),
            expression=self.generator.visit(expression) if expression is not None else "1",
        )
        self.decisions.append(decision)
        self.decision_by_node[id(node)] = decision
        return decision

    def _append_events(self, previous: list[int], event_ids: list[int]) -> list[int]:
        if not event_ids:
            return previous
        for prev in previous:
            self.edges[prev].add(event_ids[0])
        for left, right in zip(event_ids, event_ids[1:]):
            self.edges[left].add(right)
        return [event_ids[-1]]

    def _build_block(self, statements: list[c_ast.Node] | None, previous: list[int]) -> list[int]:
        exits = previous
        for statement in statements or []:
            exits = self._build_statement(statement, exits)
        return exits

    def _build_statement(self, node: c_ast.Node | None, previous: list[int]) -> list[int]:
        if node is None:
            return previous

        if isinstance(node, c_ast.Compound):
            return self._build_block(node.block_items, previous)

        if isinstance(node, c_ast.Decl):
            return self._append_events(previous, self._decl_events(node))

        if isinstance(node, c_ast.DeclList):
            exits = previous
            for declaration in node.decls:
                exits = self._append_events(exits, self._decl_events(declaration))
            return exits

        if isinstance(node, c_ast.Assignment):
            return self._append_events(previous, self._assignment_events(node))

        if isinstance(node, c_ast.Return):
            self._append_events(previous, self._expr_events(node.expr, mode="c"))
            return []

        if isinstance(node, c_ast.If):
            decision = self._new_decision(node, node.cond)
            condition_events = [self._new_point(decision.line, f"if `{decision.expression}`")]
            condition_events += self._expr_events(node.cond, mode="p", decision_id=decision.id)
            condition_exits = self._append_events(previous, condition_events)
            then_exits = self._build_statement(node.iftrue, condition_exits)
            else_exits = self._build_statement(node.iffalse, condition_exits) if node.iffalse else condition_exits
            return then_exits + else_exits

        if isinstance(node, c_ast.While):
            decision = self._new_decision(node, node.cond)
            condition_events = [self._new_point(decision.line, f"while `{decision.expression}`")]
            condition_events += self._expr_events(node.cond, mode="p", decision_id=decision.id)
            condition_exits = self._append_events(previous, condition_events)
            body_exits = self._build_statement(node.stmt, condition_exits)
            for exit_id in body_exits:
                self.edges[exit_id].add(condition_events[0])
            return condition_exits

        if isinstance(node, c_ast.For):
            exits = self._build_statement(node.init, previous) if node.init else previous
            decision = self._new_decision(node, node.cond)
            condition_events = [self._new_point(decision.line, f"for `{decision.expression}`")]
            if node.cond is not None:
                condition_events += self._expr_events(node.cond, mode="p", decision_id=decision.id)
            condition_exits = self._append_events(exits, condition_events)
            body_exits = self._build_statement(node.stmt, condition_exits)
            next_exits = self._append_events(body_exits, self._expr_events(node.next, mode="c")) if node.next else body_exits
            for exit_id in next_exits:
                self.edges[exit_id].add(condition_events[0])
            return condition_exits

        if isinstance(node, c_ast.DoWhile):
            decision = self._new_decision(node, node.cond)
            body_entry = self._new_point(self._source_line(node), "do body")
            body_exits = self._build_statement(node.stmt, self._append_events(previous, [body_entry]))
            condition_events = [self._new_point(decision.line, f"do-while `{decision.expression}`")]
            condition_events += self._expr_events(node.cond, mode="p", decision_id=decision.id)
            condition_exits = self._append_events(body_exits, condition_events)
            for exit_id in condition_exits:
                self.edges[exit_id].add(body_entry)
            return condition_exits

        if isinstance(node, c_ast.Switch):
            decision = self._new_decision(node, node.cond)
            condition_events = [self._new_point(decision.line, f"switch `{decision.expression}`")]
            condition_events += self._expr_events(node.cond, mode="p", decision_id=decision.id)
            exits = self._append_events(previous, condition_events)
            return self._build_statement(node.stmt, exits)

        if isinstance(node, c_ast.Case):
            exits = self._append_events(previous, self._expr_events(node.expr, mode="c"))
            return self._build_block(node.stmts, exits)

        if isinstance(node, c_ast.Default):
            return self._build_block(node.stmts, previous)

        if isinstance(node, c_ast.Label):
            return self._build_statement(node.stmt, previous)

        if isinstance(node, c_ast.Break):
            return []

        if isinstance(node, c_ast.Continue):
            return []

        return self._append_events(previous, self._expr_events(node, mode="c"))

    def _decl_events(self, node: c_ast.Decl) -> list[int]:
        events: list[int] = []
        if node.init is not None:
            events.extend(self._expr_events(node.init, mode="c"))
            variable = self.variable_by_name.get(node.name or "")
            if variable is not None:
                _, event_id = self._new_def(
                    variable=variable,
                    line=self._source_line(node),
                    description=f"`{variable.name}` declaration initializer",
                    node=node,
                )
                events.append(event_id)
        return events

    def _assignment_events(self, node: c_ast.Assignment) -> list[int]:
        events: list[int] = []
        variable = self._simple_lvalue_variable(node.lvalue)
        if variable is not None and node.op != "=":
            use, event_id = self._new_c_use(
                variable=variable,
                line=self._source_line(node.lvalue),
                expression=variable.name,
                node=None,
            )
            self.compound_lvalue_use_by_assignment_node[id(node)] = use
            events.append(event_id)

        events.extend(self._expr_events(node.rvalue, mode="c"))

        if variable is not None:
            _, event_id = self._new_def(
                variable=variable,
                line=self._source_line(node),
                description=f"`{variable.name}` assignment",
                node=node,
            )
            events.append(event_id)
        return events

    def _expr_events(
        self,
        node: c_ast.Node | None,
        mode: str,
        decision_id: int | None = None,
        context: str | None = None,
    ) -> list[int]:
        if node is None:
            return []

        if isinstance(node, c_ast.ID):
            variable = self.variable_by_name.get(node.name)
            if variable is None:
                return []
            expression = format_use_expression(node.name, context)
            if mode == "p":
                if decision_id is None:
                    return []
                _, event_id = self._new_p_use(
                    variable=variable,
                    line=self._source_line(node),
                    expression=expression,
                    decision_id=decision_id,
                    node=node,
                )
                return [event_id]
            _, event_id = self._new_c_use(
                variable=variable,
                line=self._source_line(node),
                expression=expression,
                node=node,
            )
            return [event_id]

        if isinstance(node, c_ast.Constant):
            return []

        if isinstance(node, c_ast.Assignment):
            return self._assignment_events(node)

        if isinstance(node, c_ast.UnaryOp) and node.op in ("++", "--", "p++", "p--"):
            variable = self._simple_lvalue_variable(node.expr)
            if variable is None:
                return self._expr_events(node.expr, mode=mode, decision_id=decision_id, context=context)
            events: list[int] = []
            use, event_id = self._new_c_use(
                variable=variable,
                line=self._source_line(node.expr),
                expression=format_use_expression(variable.name, self.generator.visit(node)),
                node=None,
            )
            self.unary_use_by_node[id(node)] = use
            events.append(event_id)
            _, def_event = self._new_def(
                variable=variable,
                line=self._source_line(node),
                description=f"`{variable.name}` {node.op}",
                node=node,
            )
            events.append(def_event)
            return events

        if isinstance(node, c_ast.TernaryOp):
            decision = self._new_decision(node, node.cond)
            events = [self._new_point(decision.line, f"ternary `{decision.expression}`")]
            events.extend(self._expr_events(node.cond, mode="p", decision_id=decision.id))
            events.extend(self._expr_events(node.iftrue, mode="c"))
            events.extend(self._expr_events(node.iffalse, mode="c"))
            return events

        if isinstance(node, c_ast.FuncCall):
            events: list[int] = []
            if node.args is not None:
                events.extend(self._expr_events(node.args, mode="c"))
            return events

        if isinstance(node, c_ast.BinaryOp):
            local_context = self.generator.visit(node)
            return (
                self._expr_events(node.left, mode=mode, decision_id=decision_id, context=local_context)
                + self._expr_events(node.right, mode=mode, decision_id=decision_id, context=local_context)
            )

        if isinstance(node, c_ast.UnaryOp):
            local_context = self.generator.visit(node)
            return self._expr_events(node.expr, mode=mode, decision_id=decision_id, context=local_context)

        if isinstance(node, c_ast.Cast):
            local_context = self.generator.visit(node)
            return self._expr_events(node.expr, mode=mode, decision_id=decision_id, context=local_context)

        events: list[int] = []
        for _, child in node.children():
            events.extend(self._expr_events(child, mode=mode, decision_id=decision_id, context=context))
        return events

    def _simple_lvalue_variable(self, node: c_ast.Node | None) -> VariableInfo | None:
        if isinstance(node, c_ast.ID):
            return self.variable_by_name.get(node.name)
        return None

    def _compute_static_obligations(self) -> StaticObligations:
        predecessors: dict[int, set[int]] = defaultdict(set)
        for source, targets in self.edges.items():
            for target in targets:
                predecessors[target].add(source)

        in_defs = [set() for _ in self.events]
        out_defs = [set() for _ in self.events]
        def_var = {definition.id: definition.var_id for definition in self.defs}

        changed = True
        while changed:
            changed = False
            for event in self.events:
                incoming: set[int] = set()
                for predecessor in predecessors[event.id]:
                    incoming.update(out_defs[predecessor])
                if incoming != in_defs[event.id]:
                    in_defs[event.id] = incoming
                    changed = True

                outgoing = set(incoming)
                if event.kind == "def" and event.def_id is not None and event.var_id is not None:
                    outgoing = {definition_id for definition_id in outgoing if def_var[definition_id] != event.var_id}
                    outgoing.add(event.def_id)
                if outgoing != out_defs[event.id]:
                    out_defs[event.id] = outgoing
                    changed = True

        c_obligations: set[tuple[int, int]] = set()
        p_obligations: set[tuple[int, int, int]] = set()
        c_uses_by_def: dict[int, set[int]] = defaultdict(set)
        p_uses_by_def: dict[int, set[tuple[int, int]]] = defaultdict(set)

        for event in self.events:
            if event.kind == "c-use" and event.c_use_id is not None and event.var_id is not None:
                for definition_id in in_defs[event.id]:
                    if def_var[definition_id] == event.var_id:
                        c_obligations.add((definition_id, event.c_use_id))
                        c_uses_by_def[definition_id].add(event.c_use_id)
            elif event.kind == "p-use" and event.p_use_id is not None and event.var_id is not None:
                for definition_id in in_defs[event.id]:
                    if def_var[definition_id] == event.var_id:
                        for outcome in (0, 1):
                            p_obligations.add((definition_id, event.p_use_id, outcome))
                            p_uses_by_def[definition_id].add((event.p_use_id, outcome))

        def_has_obligation = {
            definition.id: bool(c_uses_by_def.get(definition.id) or p_uses_by_def.get(definition.id))
            for definition in self.defs
        }
        defs_with_no_reachable_use = {
            definition.id
            for definition in self.defs
            if not def_has_obligation[definition.id]
        }

        return StaticObligations(
            c_uses=c_obligations,
            p_uses=p_obligations,
            defs_with_no_reachable_use=defs_with_no_reachable_use,
            def_has_obligation=def_has_obligation,
            c_uses_by_def=c_uses_by_def,
            p_uses_by_def=p_uses_by_def,
        )


class DataFlowGenerator(c_generator.CGenerator):
    def __init__(self, analysis: DataFlowAnalyzer) -> None:
        super().__init__()
        self.analysis = analysis
        self.expression_mode: str | None = None

    def _with_mode(self, mode: str | None, node: c_ast.Node | None) -> str:
        if node is None:
            return ""
        old_mode = self.expression_mode
        self.expression_mode = mode
        try:
            return self.visit(node)
        finally:
            self.expression_mode = old_mode

    def visit_FuncDef(self, node: c_ast.FuncDef) -> str:
        decl = self.visit(node.decl)
        self.indent_level = 0
        lines = [decl, "{\n"]
        self.indent_level = 2
        lines.append(self._make_indent() + "__df_reset_current();\n")
        for definition in self.analysis.parameter_defs:
            lines.append(self._make_indent() + self._def_call(definition) + ";\n")
        for statement in node.body.block_items or []:
            lines.append(self._generate_stmt(statement))
        self.indent_level = 0
        lines.append("}\n")
        return "".join(lines)

    def _generate_stmt(self, node: c_ast.Node, add_indent: bool = False) -> str:
        typ = type(node)
        if add_indent:
            self.indent_level += 2
        indent = self._make_indent()
        if add_indent:
            self.indent_level -= 2

        if isinstance(node, c_ast.Decl):
            definition = self.analysis.def_by_decl_node.get(id(node))
            result = indent + self.visit(node) + ";\n"
            if definition is not None:
                result += indent + self._def_call(definition) + ";\n"
            return result

        if isinstance(node, c_ast.Assignment):
            definition = self.analysis.def_by_assignment_node.get(id(node))
            lvalue_use = self.analysis.compound_lvalue_use_by_assignment_node.get(id(node))
            result = ""
            if lvalue_use is not None:
                result += indent + self._c_use_call(lvalue_use) + ";\n"
            result += indent + self.visit(node) + ";\n"
            if definition is not None:
                result += indent + self._def_call(definition) + ";\n"
            return result

        if isinstance(node, c_ast.UnaryOp) and node.op in ("++", "--", "p++", "p--"):
            use = self.analysis.unary_use_by_node.get(id(node))
            definition = self.analysis.def_by_unary_node.get(id(node))
            result = ""
            if use is not None:
                result += indent + self._c_use_call(use) + ";\n"
            result += indent + self.visit(node) + ";\n"
            if definition is not None:
                result += indent + self._def_call(definition) + ";\n"
            return result

        if typ in (
            c_ast.Cast,
            c_ast.BinaryOp,
            c_ast.TernaryOp,
            c_ast.FuncCall,
            c_ast.ArrayRef,
            c_ast.StructRef,
            c_ast.Constant,
            c_ast.ID,
            c_ast.Typedef,
            c_ast.ExprList,
        ):
            return indent + self._with_mode("c", node) + ";\n"
        if typ in (c_ast.Compound,):
            return self.visit(node)
        if typ in (c_ast.If,):
            return indent + self.visit(node)
        return indent + self.visit(node) + "\n"

    def visit_Decl(self, node: c_ast.Decl, no_type: bool = False) -> str:
        if no_type:
            result = node.name
        else:
            result = self._generate_decl(node)
        if node.bitsize:
            result += " : " + self.visit(node.bitsize)
        if node.init:
            result += " = " + self._with_mode("c", node.init)
        return result

    def visit_Return(self, node: c_ast.Return) -> str:
        result = "return"
        if node.expr:
            result += " " + self._with_mode("c", node.expr)
        return result + ";"

    def visit_Assignment(self, node: c_ast.Assignment) -> str:
        rval = self._with_mode("c", node.rvalue)
        return f"{self._plain_lvalue(node.lvalue)} {node.op} {rval}"

    def visit_UnaryOp(self, node: c_ast.UnaryOp) -> str:
        if node.op not in ("++", "--", "p++", "p--"):
            return super().visit_UnaryOp(node)

        variable = self.analysis._simple_lvalue_variable(node.expr)
        use = self.analysis.unary_use_by_node.get(id(node))
        definition = self.analysis.def_by_unary_node.get(id(node))
        if variable is None or use is None or definition is None:
            return super().visit_UnaryOp(node)

        expression = self._plain_lvalue(node.expr)
        if node.op == "++":
            operation = f"++{expression}"
        elif node.op == "--":
            operation = f"--{expression}"
        elif node.op == "p++":
            operation = f"{expression}++"
        else:
            operation = f"{expression}--"
        return (
            "({ "
            f"{self._c_use_call(use)}; "
            f"__typeof__({expression}) __df_tmp = {operation}; "
            f"{self._def_call(definition)}; "
            "__df_tmp; })"
        )

    def visit_ID(self, node: c_ast.ID) -> str:
        use = self.analysis.use_by_id_node.get(id(node))
        if use is None:
            return node.name
        if self.expression_mode == "p" and use.kind == "p-use":
            return f"({self._p_use_call(use)}, {node.name})"
        if self.expression_mode == "c" and use.kind == "c-use":
            return f"({self._c_use_call(use)}, {node.name})"
        return node.name

    def visit_If(self, node: c_ast.If) -> str:
        condition = self._predicate_expression(node, node.cond)
        result = f"if ({condition})\n"
        result += self._generate_control_body(node.iftrue)
        if node.iffalse:
            result += self._make_indent() + "else\n"
            result += self._generate_control_body(node.iffalse)
        return result

    def visit_While(self, node: c_ast.While) -> str:
        condition = self._predicate_expression(node, node.cond)
        result = f"while ({condition})\n"
        result += self._generate_control_body(node.stmt)
        return result

    def visit_For(self, node: c_ast.For) -> str:
        result = "{\n"
        self.indent_level += 2
        if node.init:
            if isinstance(node.init, c_ast.DeclList):
                for declaration in node.init.decls:
                    result += self._generate_stmt(declaration)
            else:
                result += self._generate_stmt(node.init)
        condition = self._predicate_expression(node, node.cond) if node.cond is not None else "1"
        result += self._make_indent() + f"while ({condition})\n"
        result += self._generate_for_body(node.stmt, node.next)
        self.indent_level -= 2
        result += self._make_indent() + "}\n"
        return result

    def visit_DoWhile(self, node: c_ast.DoWhile) -> str:
        result = "do\n"
        result += self._generate_control_body(node.stmt)
        condition = self._predicate_expression(node, node.cond)
        result += self._make_indent() + f"while ({condition});"
        return result

    def visit_TernaryOp(self, node: c_ast.TernaryOp) -> str:
        condition = self._predicate_expression(node, node.cond)
        return f"({condition}) ? ({self._with_mode('c', node.iftrue)}) : ({self._with_mode('c', node.iffalse)})"

    def _generate_control_body(self, node: c_ast.Node | None) -> str:
        if node is None:
            return self._make_indent() + "  ;\n"
        if isinstance(node, c_ast.Compound):
            return self._generate_stmt(node, add_indent=True)

        self.indent_level += 2
        result = self._make_indent() + "{\n"
        self.indent_level += 2
        result += self._generate_stmt(node)
        self.indent_level -= 2
        result += self._make_indent() + "}\n"
        self.indent_level -= 2
        return result

    def _generate_for_body(self, body: c_ast.Node | None, next_expr: c_ast.Node | None) -> str:
        self.indent_level += 2
        result = self._make_indent() + "{\n"
        self.indent_level += 2
        if isinstance(body, c_ast.Compound):
            for statement in body.block_items or []:
                result += self._generate_stmt(statement)
        elif body is not None:
            result += self._generate_stmt(body)
        if next_expr is not None:
            result += self._generate_stmt(next_expr)
        self.indent_level -= 2
        result += self._make_indent() + "}\n"
        self.indent_level -= 2
        return result

    def _predicate_expression(self, node: c_ast.Node, condition: c_ast.Node | None) -> str:
        decision = self.analysis.decision_by_node.get(id(node))
        if decision is None or condition is None:
            return self._with_mode("p", condition) if condition is not None else "1"
        condition_text = self._with_mode("p", condition)
        return (
            "({ "
            f"__df_begin_pred({decision.id}); "
            f"int __df_result = !!({condition_text}); "
            f"__df_end_pred({decision.id}, __df_result); "
            "__df_result; })"
        )

    def _plain_lvalue(self, node: c_ast.Node) -> str:
        old_mode = self.expression_mode
        self.expression_mode = None
        try:
            return self.visit(node)
        finally:
            self.expression_mode = old_mode

    def _def_call(self, definition: DefInfo) -> str:
        return f"__df_record_def({definition.var_id}, {definition.id})"

    def _c_use_call(self, use: UseInfo) -> str:
        return f"__df_record_cuse({use.id}, {use.var_id})"

    def _p_use_call(self, use: UseInfo) -> str:
        return f"__df_touch_puse({use.id}, {use.var_id})"


def generate_runtime_header(var_count: int, def_count: int, c_use_count: int, p_use_count: int) -> str:
    var_dim = max(1, var_count)
    def_dim = max(1, def_count)
    c_dim = max(1, c_use_count)
    p_dim = max(1, p_use_count)
    return f"""\
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <limits.h>
#include <float.h>

#define __DF_VAR_COUNT {var_count}
#define __DF_DEF_COUNT {def_count}
#define __DF_C_USE_COUNT {c_use_count}
#define __DF_P_USE_COUNT {p_use_count}

static int __df_current_def[{var_dim}];
static unsigned char __df_c_seen[{def_dim}][{c_dim}];
static int __df_c_case[{def_dim}][{c_dim}];
static unsigned char __df_p_seen[{def_dim}][{p_dim}][2];
static int __df_p_case[{def_dim}][{p_dim}][2];
static unsigned char __df_p_touched[{p_dim}];
static int __df_p_touched_def[{p_dim}];
static int __df_current_case = -1;

static void __df_init_once(void) {{
    int i;
    int j;
    int k;
    for (i = 0; i < __DF_DEF_COUNT; ++i) {{
        for (j = 0; j < __DF_C_USE_COUNT; ++j) {{
            __df_c_case[i][j] = -1;
        }}
        for (j = 0; j < __DF_P_USE_COUNT; ++j) {{
            for (k = 0; k < 2; ++k) {{
                __df_p_case[i][j][k] = -1;
            }}
        }}
    }}
}}

static void __df_start_case(int case_index) {{
    __df_current_case = case_index;
}}

static void __df_reset_current(void) {{
    int i;
    for (i = 0; i < __DF_VAR_COUNT; ++i) {{
        __df_current_def[i] = -1;
    }}
}}

static void __df_record_def(int var_id, int def_id) {{
    if (var_id >= 0 && var_id < __DF_VAR_COUNT) {{
        __df_current_def[var_id] = def_id;
    }}
}}

static void __df_record_cuse(int use_id, int var_id) {{
    int def_id;
    if (use_id < 0 || use_id >= __DF_C_USE_COUNT || var_id < 0 || var_id >= __DF_VAR_COUNT) {{
        return;
    }}
    def_id = __df_current_def[var_id];
    if (def_id < 0 || def_id >= __DF_DEF_COUNT) {{
        return;
    }}
    __df_c_seen[def_id][use_id] = 1;
    if (__df_c_case[def_id][use_id] < 0) {{
        __df_c_case[def_id][use_id] = __df_current_case;
    }}
}}

static void __df_begin_pred(int decision_id) {{
    int i;
    (void)decision_id;
    for (i = 0; i < __DF_P_USE_COUNT; ++i) {{
        __df_p_touched[i] = 0;
        __df_p_touched_def[i] = -1;
    }}
}}

static void __df_touch_puse(int use_id, int var_id) {{
    int def_id;
    if (use_id < 0 || use_id >= __DF_P_USE_COUNT || var_id < 0 || var_id >= __DF_VAR_COUNT) {{
        return;
    }}
    def_id = __df_current_def[var_id];
    if (def_id < 0 || def_id >= __DF_DEF_COUNT) {{
        return;
    }}
    __df_p_touched[use_id] = 1;
    __df_p_touched_def[use_id] = def_id;
}}

static void __df_end_pred(int decision_id, int result) {{
    int i;
    int outcome = !!result;
    (void)decision_id;
    for (i = 0; i < __DF_P_USE_COUNT; ++i) {{
        int def_id;
        if (!__df_p_touched[i]) {{
            continue;
        }}
        def_id = __df_p_touched_def[i];
        if (def_id < 0 || def_id >= __DF_DEF_COUNT) {{
            continue;
        }}
        __df_p_seen[def_id][i][outcome] = 1;
        if (__df_p_case[def_id][i][outcome] < 0) {{
            __df_p_case[def_id][i][outcome] = __df_current_case;
        }}
    }}
}}

static void __df_dump(void) {{
    int i;
    int j;
    int k;
    for (i = 0; i < __DF_DEF_COUNT; ++i) {{
        for (j = 0; j < __DF_C_USE_COUNT; ++j) {{
            if (__df_c_seen[i][j]) {{
                printf("C %d %d %d\\n", i, j, __df_c_case[i][j]);
            }}
        }}
        for (j = 0; j < __DF_P_USE_COUNT; ++j) {{
            for (k = 0; k < 2; ++k) {{
                if (__df_p_seen[i][j][k]) {{
                    printf("P %d %d %d %d\\n", i, j, k, __df_p_case[i][j][k]);
                }}
            }}
        }}
    }}
}}
"""


def generate_harness(
    function: c_ast.FuncDef,
    analysis: DataFlowAnalyzer,
    parameters: list[ParameterInfo],
    cases: list[list[Any]],
) -> str:
    runtime = generate_runtime_header(
        var_count=len(analysis.variables),
        def_count=len(analysis.defs),
        c_use_count=len(analysis.c_uses),
        p_use_count=len(analysis.p_uses),
    )
    instrumented_function = DataFlowGenerator(analysis).visit(function)
    calls = ["    __df_init_once();"]
    name = function_name(function)
    for index, case in enumerate(cases):
        args = []
        for value, parameter in zip(case, parameters):
            literal = value_to_c_literal(value, parameter.type_name)
            args.append(f"(({parameter.type_name})({literal}))")
        calls.append(f"    __df_start_case({index});")
        calls.append(f"    (void){name}({', '.join(args)});")
    if not cases:
        calls.append("    /* no cases supplied */")

    main = "\n".join(
        [
            "int main(void) {",
            *calls,
            "    __df_dump();",
            "    return 0;",
            "}",
            "",
        ]
    )
    return runtime + "\n" + instrumented_function + "\n" + main


def compile_and_run(source: str, build_dir: Path, timeout: float) -> str:
    generated_c = build_dir / "data_flow_instrumented.c"
    binary = build_dir / "data_flow_harness"
    generated_c.write_text(source, encoding="utf-8")

    compile_cmd = [
        "gcc",
        "-std=gnu11",
        "-O0",
        "-Wall",
        "-Wextra",
        str(generated_c),
        "-o",
        str(binary),
    ]
    compile_result = subprocess.run(compile_cmd, text=True, capture_output=True)
    if compile_result.returncode != 0:
        raise SystemExit(
            "Compilation failed.\n"
            f"Command: {' '.join(compile_cmd)}\n"
            f"{compile_result.stderr}"
        )

    try:
        run_result = subprocess.run([str(binary)], text=True, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        raise SystemExit(f"Instrumented program timed out after {timeout} seconds.") from exc

    if run_result.returncode != 0:
        raise SystemExit(
            "Instrumented program exited with a non-zero status.\n"
            f"stdout:\n{run_result.stdout}\n"
            f"stderr:\n{run_result.stderr}"
        )
    return run_result.stdout


def parse_runtime_output(output: str) -> RuntimeData:
    c_uses: set[tuple[int, int]] = set()
    p_uses: set[tuple[int, int, int]] = set()
    c_case: dict[tuple[int, int], int] = {}
    p_case: dict[tuple[int, int, int], int] = {}

    for raw_line in output.splitlines():
        parts = raw_line.split()
        if not parts:
            continue
        if parts[0] == "C":
            key = (int(parts[1]), int(parts[2]))
            c_uses.add(key)
            c_case[key] = int(parts[3])
        elif parts[0] == "P":
            key = (int(parts[1]), int(parts[2]), int(parts[3]))
            p_uses.add(key)
            p_case[key] = int(parts[4])

    return RuntimeData(c_uses=c_uses, p_uses=p_uses, c_case=c_case, p_case=p_case)


def build_report(
    source: str,
    function: c_ast.FuncDef,
    parameters: list[ParameterInfo],
    cases: list[list[Any]],
    analysis: DataFlowAnalyzer,
    obligations: StaticObligations,
    runtime: RuntimeData,
) -> str:
    source_lines = source.splitlines()
    signature = ", ".join(f"{param.type_name} {param.name}" for param in parameters) or "void"
    lines = [
        f"Function: {function_name(function)}({signature})",
        f"Cases: {len(cases)}",
        f"Tracked variables: {len(analysis.variables)}",
        f"Definitions: {len(analysis.defs)}",
        f"C-uses: {len(analysis.c_uses)}",
        f"P-uses: {len(analysis.p_uses)}",
        "",
    ]

    missing_all_defs = missing_all_defs_obligations(analysis, obligations, runtime)
    append_all_defs_report(lines, source_lines, "All-defs", missing_all_defs, analysis)

    missing_c = sorted(obligations.c_uses - runtime.c_uses)
    append_c_use_report(lines, source_lines, "All-c-uses", missing_c, analysis)

    missing_p = sorted(obligations.p_uses - runtime.p_uses)
    append_p_use_report(lines, source_lines, "All-p-uses", missing_p, analysis)

    missing_mixed = missing_all_p_some_c_obligations(analysis, obligations, runtime)
    append_mixed_report(lines, source_lines, "All-p-uses/some-c-uses", missing_mixed, analysis)

    lines.append("Note: missing entries are data-flow obligations not covered by any supplied input case.")
    return "\n".join(lines)


def missing_all_defs_obligations(
    analysis: DataFlowAnalyzer,
    obligations: StaticObligations,
    runtime: RuntimeData,
) -> list[int]:
    covered_defs = {definition_id for definition_id, _ in runtime.c_uses}
    covered_defs.update(definition_id for definition_id, _, _ in runtime.p_uses)
    missing = []
    for definition in analysis.defs:
        if definition.id in obligations.defs_with_no_reachable_use:
            missing.append(definition.id)
        elif definition.id not in covered_defs:
            missing.append(definition.id)
    return missing


def missing_all_p_some_c_obligations(
    analysis: DataFlowAnalyzer,
    obligations: StaticObligations,
    runtime: RuntimeData,
) -> dict[int, dict[str, Any]]:
    missing: dict[int, dict[str, Any]] = {}
    for definition in analysis.defs:
        p_requirements = obligations.p_uses_by_def.get(definition.id, set())
        c_requirements = obligations.c_uses_by_def.get(definition.id, set())
        if p_requirements:
            missing_p = {
                (definition.id, use_id, outcome)
                for use_id, outcome in p_requirements
                if (definition.id, use_id, outcome) not in runtime.p_uses
            }
            if missing_p:
                missing[definition.id] = {"kind": "missing-p-uses", "p": sorted(missing_p)}
        elif c_requirements:
            has_some_c = any((definition.id, use_id) in runtime.c_uses for use_id in c_requirements)
            if not has_some_c:
                missing[definition.id] = {"kind": "missing-some-c-use", "c": sorted(c_requirements)}
        else:
            missing[definition.id] = {"kind": "no-reachable-use"}
    return missing


def append_all_defs_report(
    lines: list[str],
    source_lines: list[str],
    title: str,
    missing_defs: list[int],
    analysis: DataFlowAnalyzer,
) -> None:
    if not missing_defs:
        lines.append(f"{title}: covered")
        lines.append("")
        return
    lines.append(f"{title}: not covered")
    for definition_id in missing_defs:
        definition = analysis.defs[definition_id]
        lines.append(format_definition_line(source_lines, definition))
        lines.append("    no covered def-clear use from this definition")
    lines.append("")


def append_c_use_report(
    lines: list[str],
    source_lines: list[str],
    title: str,
    missing: list[tuple[int, int]],
    analysis: DataFlowAnalyzer,
) -> None:
    if not missing:
        lines.append(f"{title}: covered")
        lines.append("")
        return
    lines.append(f"{title}: not covered")
    for definition_id, use_id in missing:
        lines.extend(format_c_obligation(source_lines, analysis, definition_id, use_id))
    lines.append("")


def append_p_use_report(
    lines: list[str],
    source_lines: list[str],
    title: str,
    missing: list[tuple[int, int, int]],
    analysis: DataFlowAnalyzer,
) -> None:
    if not missing:
        lines.append(f"{title}: covered")
        lines.append("")
        return
    lines.append(f"{title}: not covered")
    for definition_id, use_id, outcome in missing:
        lines.extend(format_p_obligation(source_lines, analysis, definition_id, use_id, outcome))
    lines.append("")


def append_mixed_report(
    lines: list[str],
    source_lines: list[str],
    title: str,
    missing: dict[int, dict[str, Any]],
    analysis: DataFlowAnalyzer,
) -> None:
    if not missing:
        lines.append(f"{title}: covered")
        lines.append("")
        return
    lines.append(f"{title}: not covered")
    for definition_id, detail in sorted(missing.items()):
        definition = analysis.defs[definition_id]
        if detail["kind"] == "missing-p-uses":
            lines.append(format_definition_line(source_lines, definition))
            lines.append("    missing required p-use outcome(s):")
            for _, use_id, outcome in detail["p"]:
                use = analysis.p_uses[use_id]
                lines.append(format_use_line(source_lines, use, outcome=outcome))
        elif detail["kind"] == "missing-some-c-use":
            lines.append(format_definition_line(source_lines, definition))
            lines.append("    no covered c-use fallback; possible c-use(s):")
            for use_id in detail["c"]:
                use = analysis.c_uses[use_id]
                lines.append(format_use_line(source_lines, use))
        else:
            lines.append(format_definition_line(source_lines, definition))
            lines.append("    no statically reachable c-use or p-use")
    lines.append("")


def format_c_obligation(
    source_lines: list[str],
    analysis: DataFlowAnalyzer,
    definition_id: int,
    use_id: int,
) -> list[str]:
    definition = analysis.defs[definition_id]
    use = analysis.c_uses[use_id]
    return [
        f"  missing data-flow case: `{definition.var_name}` def -> c-use",
        format_definition_line(source_lines, definition, indent="    "),
        format_use_line(source_lines, use, indent="    "),
    ]


def format_p_obligation(
    source_lines: list[str],
    analysis: DataFlowAnalyzer,
    definition_id: int,
    use_id: int,
    outcome: int,
) -> list[str]:
    definition = analysis.defs[definition_id]
    use = analysis.p_uses[use_id]
    return [
        f"  missing data-flow case: `{definition.var_name}` def -> p-use outcome {outcome_name(outcome)}",
        format_definition_line(source_lines, definition, indent="    "),
        format_use_line(source_lines, use, indent="    ", outcome=outcome),
    ]


def format_definition_line(source_lines: list[str], definition: DefInfo, indent: str = "  ") -> str:
    excerpt = source_excerpt(source_lines, definition.line)
    return (
        f"{indent}def line {definition.line}: {definition.description}; "
        f"source: {excerpt}"
    )


def format_use_line(source_lines: list[str], use: UseInfo, indent: str = "    ", outcome: int | None = None) -> str:
    excerpt = source_excerpt(source_lines, use.line)
    suffix = f"; outcome {outcome_name(outcome)}" if outcome is not None else ""
    return (
        f"{indent}{use.kind} line {use.line}: `{use.expression}`{suffix}; "
        f"source: {excerpt}"
    )


def outcome_name(outcome: int | None) -> str:
    if outcome is None:
        return ""
    return "true" if outcome else "false"


def build_json_report(
    source: str,
    function: c_ast.FuncDef,
    parameters: list[ParameterInfo],
    cases: list[list[Any]],
    analysis: DataFlowAnalyzer,
    obligations: StaticObligations,
    runtime: RuntimeData,
) -> dict[str, Any]:
    source_lines = source.splitlines()
    missing_defs = missing_all_defs_obligations(analysis, obligations, runtime)
    missing_c = sorted(obligations.c_uses - runtime.c_uses)
    missing_p = sorted(obligations.p_uses - runtime.p_uses)
    missing_mixed = missing_all_p_some_c_obligations(analysis, obligations, runtime)

    return {
        "function": function_name(function),
        "parameters": [parameter.__dict__ for parameter in parameters],
        "case_count": len(cases),
        "variables": [variable.__dict__ for variable in analysis.variables],
        "definitions": [definition.__dict__ for definition in analysis.defs],
        "c_uses": [use.__dict__ for use in analysis.c_uses],
        "p_uses": [use.__dict__ for use in analysis.p_uses],
        "coverage": {
            "all_defs": {
                "covered": not missing_defs,
                "missing": [definition_to_json(source_lines, analysis.defs[definition_id]) for definition_id in missing_defs],
            },
            "all_c_uses": {
                "covered": not missing_c,
                "missing": [
                    c_obligation_to_json(source_lines, analysis, definition_id, use_id)
                    for definition_id, use_id in missing_c
                ],
            },
            "all_p_uses": {
                "covered": not missing_p,
                "missing": [
                    p_obligation_to_json(source_lines, analysis, definition_id, use_id, outcome)
                    for definition_id, use_id, outcome in missing_p
                ],
            },
            "all_p_uses_some_c_uses": {
                "covered": not missing_mixed,
                "missing": {
                    str(definition_id): mixed_missing_to_json(source_lines, analysis, detail)
                    for definition_id, detail in sorted(missing_mixed.items())
                },
            },
        },
    }


def definition_to_json(source_lines: list[str], definition: DefInfo) -> dict[str, Any]:
    return {
        "id": definition.id,
        "variable": definition.var_name,
        "line": definition.line,
        "description": definition.description,
        "source": source_excerpt(source_lines, definition.line),
    }


def use_to_json(source_lines: list[str], use: UseInfo, outcome: int | None = None) -> dict[str, Any]:
    result = {
        "id": use.id,
        "variable": use.var_name,
        "line": use.line,
        "kind": use.kind,
        "expression": use.expression,
        "source": source_excerpt(source_lines, use.line),
    }
    if outcome is not None:
        result["outcome"] = outcome_name(outcome)
    return result


def c_obligation_to_json(
    source_lines: list[str],
    analysis: DataFlowAnalyzer,
    definition_id: int,
    use_id: int,
) -> dict[str, Any]:
    return {
        "definition": definition_to_json(source_lines, analysis.defs[definition_id]),
        "use": use_to_json(source_lines, analysis.c_uses[use_id]),
    }


def p_obligation_to_json(
    source_lines: list[str],
    analysis: DataFlowAnalyzer,
    definition_id: int,
    use_id: int,
    outcome: int,
) -> dict[str, Any]:
    return {
        "definition": definition_to_json(source_lines, analysis.defs[definition_id]),
        "use": use_to_json(source_lines, analysis.p_uses[use_id], outcome=outcome),
    }


def mixed_missing_to_json(source_lines: list[str], analysis: DataFlowAnalyzer, detail: dict[str, Any]) -> dict[str, Any]:
    if detail["kind"] == "missing-p-uses":
        return {
            "kind": detail["kind"],
            "p_uses": [
                p_obligation_to_json(source_lines, analysis, definition_id, use_id, outcome)
                for definition_id, use_id, outcome in detail["p"]
            ],
        }
    if detail["kind"] == "missing-some-c-use":
        return {
            "kind": detail["kind"],
            "candidate_c_uses": [
                use_to_json(source_lines, analysis.c_uses[use_id])
                for use_id in detail["c"]
            ],
        }
    return {"kind": detail["kind"]}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check data-flow coverage for one C function.")
    parser.add_argument("source", nargs="?", default="input.c", help="C file containing exactly one function. Default: input.c")
    parser.add_argument("cases", nargs="?", default="cases.json", help="JSON file with test cases. Default: cases.json")
    parser.add_argument("--json", action="store_true", help="Print machine-readable JSON instead of the text report.")
    parser.add_argument("--keep", action="store_true", help="Keep the generated instrumented C file and harness binary.")
    parser.add_argument("--timeout", type=float, default=5.0, help="Timeout in seconds for running the instrumented program.")
    args = parser.parse_args(argv)

    source_path = Path(args.source)
    cases_path = Path(args.cases)
    source, _, function = parse_c_file(source_path)
    parameters = function_parameters(function)
    cases = load_cases(cases_path, parameters)

    analysis = DataFlowAnalyzer(function, parameters, PARSER_PREFIX_LINES)
    obligations = analysis.analyze()
    harness = generate_harness(function, analysis, parameters, cases)

    if args.keep:
        build_dir = Path(".data_flow_build")
        if build_dir.exists():
            shutil.rmtree(build_dir)
        build_dir.mkdir(parents=True)
        output = compile_and_run(harness, build_dir, timeout=args.timeout)
        kept_dir: Path | None = build_dir
    else:
        with tempfile.TemporaryDirectory(prefix="data_flow_check_") as tmp:
            output = compile_and_run(harness, Path(tmp), timeout=args.timeout)
        kept_dir = None

    runtime = parse_runtime_output(output)
    if args.json:
        print(json.dumps(build_json_report(source, function, parameters, cases, analysis, obligations, runtime), indent=2))
    else:
        print(build_report(source, function, parameters, cases, analysis, obligations, runtime))
        if kept_dir is not None:
            print(f"Kept generated files in {kept_dir}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
