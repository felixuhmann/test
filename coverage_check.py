#!/usr/bin/env python3
"""
Dynamic source-line coverage checker for one C function.

The checker parses input.c, instruments the single function, compiles a small
test harness, runs the provided cases, and reports missing statement, decision,
condition, and MC/DC coverage objectives.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pycparser import c_ast, c_generator, c_parser


PARSER_PREFIX = """\
typedef _Bool bool;
typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef long long int64_t;
typedef unsigned long long uint64_t;
typedef unsigned long size_t;
"""
PARSER_PREFIX_LINES = PARSER_PREFIX.count("\n")


@dataclass(frozen=True)
class ParameterInfo:
    name: str
    type_name: str


@dataclass(frozen=True)
class StatementInfo:
    id: int
    line: int


@dataclass(frozen=True)
class ConditionInfo:
    id: int
    line: int
    expression: str


@dataclass(frozen=True)
class DecisionInfo:
    id: int
    line: int
    expression: str
    conditions: list[ConditionInfo]


class CoverageAnalyzer:
    def __init__(self, line_offset: int) -> None:
        self.line_offset = line_offset
        self.generator = c_generator.CGenerator()
        self.statements: list[StatementInfo] = []
        self.decisions: list[DecisionInfo] = []
        self.statement_by_node: dict[int, StatementInfo] = {}
        self.decision_by_node: dict[int, DecisionInfo] = {}

    def analyze_function(self, function: c_ast.FuncDef) -> None:
        self._analyze_statement(function.body)

    def _source_line(self, node: c_ast.Node | None) -> int:
        coord = getattr(node, "coord", None)
        if coord is None or coord.line is None:
            return 0
        return max(0, coord.line - self.line_offset)

    def _add_statement(self, node: c_ast.Node) -> None:
        if id(node) in self.statement_by_node:
            return
        line = self._source_line(node)
        if line <= 0:
            return
        info = StatementInfo(id=len(self.statements), line=line)
        self.statements.append(info)
        self.statement_by_node[id(node)] = info

    def _add_decision(self, node: c_ast.Node, condition: c_ast.Node | None) -> None:
        if condition is None or id(node) in self.decision_by_node:
            return

        leaves = self._condition_leaves(condition)
        conditions: list[ConditionInfo] = []
        for index, leaf in enumerate(leaves):
            line = self._source_line(leaf) or self._source_line(node)
            conditions.append(
                ConditionInfo(
                    id=index,
                    line=line,
                    expression=self.generator.visit(leaf),
                )
            )

        info = DecisionInfo(
            id=len(self.decisions),
            line=self._source_line(node) or self._source_line(condition),
            expression=self.generator.visit(condition),
            conditions=conditions,
        )
        self.decisions.append(info)
        self.decision_by_node[id(node)] = info

    def _condition_leaves(self, node: c_ast.Node) -> list[c_ast.Node]:
        if isinstance(node, c_ast.BinaryOp) and node.op in ("&&", "||"):
            return self._condition_leaves(node.left) + self._condition_leaves(node.right)
        return [node]

    def _analyze_expression(self, node: c_ast.Node | None) -> None:
        if node is None:
            return
        if isinstance(node, c_ast.TernaryOp):
            self._add_decision(node, node.cond)
            self._analyze_expression(node.cond)
            self._analyze_expression(node.iftrue)
            self._analyze_expression(node.iffalse)
            return
        for _, child in node.children():
            self._analyze_expression(child)

    def _analyze_statement(self, node: c_ast.Node | None) -> None:
        if node is None:
            return

        if isinstance(node, c_ast.Compound):
            for item in node.block_items or []:
                self._analyze_statement(item)
            return

        if isinstance(node, c_ast.If):
            self._add_statement(node)
            self._add_decision(node, node.cond)
            self._analyze_expression(node.cond)
            self._analyze_statement(node.iftrue)
            self._analyze_statement(node.iffalse)
            return

        if isinstance(node, c_ast.While):
            self._add_statement(node)
            self._add_decision(node, node.cond)
            self._analyze_expression(node.cond)
            self._analyze_statement(node.stmt)
            return

        if isinstance(node, c_ast.For):
            self._add_statement(node)
            self._analyze_expression(node.init)
            if node.cond is not None:
                self._add_decision(node, node.cond)
                self._analyze_expression(node.cond)
            self._analyze_expression(node.next)
            self._analyze_statement(node.stmt)
            return

        if isinstance(node, c_ast.DoWhile):
            self._add_statement(node)
            self._analyze_statement(node.stmt)
            self._add_decision(node, node.cond)
            self._analyze_expression(node.cond)
            return

        if isinstance(node, c_ast.Switch):
            self._add_statement(node)
            self._analyze_expression(node.cond)
            self._analyze_statement(node.stmt)
            return

        if isinstance(node, c_ast.Case):
            self._analyze_expression(node.expr)
            for stmt in node.stmts or []:
                self._analyze_statement(stmt)
            return

        if isinstance(node, c_ast.Default):
            for stmt in node.stmts or []:
                self._analyze_statement(stmt)
            return

        if isinstance(node, c_ast.Label):
            self._analyze_statement(node.stmt)
            return

        if not isinstance(node, c_ast.EmptyStatement):
            self._add_statement(node)

        for _, child in node.children():
            self._analyze_expression(child)


class InstrumentingGenerator(c_generator.CGenerator):
    def __init__(self, analysis: CoverageAnalyzer) -> None:
        super().__init__()
        self.analysis = analysis
        self._plain_generator = c_generator.CGenerator()

    def _generate_stmt(self, n: c_ast.Node, add_indent: bool = False) -> str:
        typ = type(n)
        if add_indent:
            self.indent_level += 2
        indent = self._make_indent()
        if add_indent:
            self.indent_level -= 2

        prefix = self._statement_marker(n, indent)

        if typ in (
            c_ast.Decl,
            c_ast.Assignment,
            c_ast.Cast,
            c_ast.UnaryOp,
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
            return prefix + indent + self.visit(n) + ";\n"
        if typ in (c_ast.Compound,):
            return prefix + self.visit(n)
        if typ in (c_ast.If,):
            return prefix + indent + self.visit(n)
        return prefix + indent + self.visit(n) + "\n"

    def _statement_marker(self, node: c_ast.Node, indent: str) -> str:
        info = self.analysis.statement_by_node.get(id(node))
        if info is None:
            return ""
        return f"{indent}__cov_stmt({info.id});\n"

    def _generate_control_body(self, node: c_ast.Node | None) -> str:
        if node is None:
            return self._make_indent() + "  ;\n"
        if isinstance(node, c_ast.Compound):
            return self._generate_stmt(node, add_indent=True)

        self.indent_level += 2
        s = self._make_indent() + "{\n"
        self.indent_level += 2
        s += self._generate_stmt(node)
        self.indent_level -= 2
        s += self._make_indent() + "}\n"
        self.indent_level -= 2
        return s

    def visit_If(self, n: c_ast.If) -> str:
        condition = self._instrumented_decision(n, n.cond)
        s = f"if ({condition})\n"
        s += self._generate_control_body(n.iftrue)
        if n.iffalse:
            s += self._make_indent() + "else\n"
            s += self._generate_control_body(n.iffalse)
        return s

    def visit_While(self, n: c_ast.While) -> str:
        condition = self._instrumented_decision(n, n.cond)
        s = f"while ({condition})\n"
        s += self._generate_control_body(n.stmt)
        return s

    def visit_For(self, n: c_ast.For) -> str:
        s = "for ("
        if n.init:
            s += self.visit(n.init)
        s += ";"
        if n.cond:
            s += " " + self._instrumented_decision(n, n.cond)
        s += ";"
        if n.next:
            s += " " + self.visit(n.next)
        s += ")\n"
        s += self._generate_control_body(n.stmt)
        return s

    def visit_DoWhile(self, n: c_ast.DoWhile) -> str:
        s = "do\n"
        s += self._generate_control_body(n.stmt)
        condition = self._instrumented_decision(n, n.cond)
        s += self._make_indent() + f"while ({condition});"
        return s

    def visit_TernaryOp(self, n: c_ast.TernaryOp) -> str:
        condition = self._instrumented_decision(n, n.cond)
        s = f"({condition}) ? "
        s += "(" + self._visit_expr(n.iftrue) + ") : "
        s += "(" + self._visit_expr(n.iffalse) + ")"
        return s

    def _instrumented_decision(self, node: c_ast.Node, condition: c_ast.Node | None) -> str:
        info = self.analysis.decision_by_node.get(id(node))
        if info is None or condition is None:
            return self.visit(condition) if condition is not None else "1"

        leaves = self.analysis._condition_leaves(condition)
        leaf_indexes = {id(leaf): index for index, leaf in enumerate(leaves)}

        def rebuilt_expression(expr: c_ast.Node) -> str:
            if isinstance(expr, c_ast.BinaryOp) and expr.op in ("&&", "||"):
                return f"({rebuilt_expression(expr.left)} {expr.op} {rebuilt_expression(expr.right)})"
            return f"__cov_d{info.id}_c{leaf_indexes[id(expr)]}"

        lines: list[str] = ["({ "]
        for index, leaf in enumerate(leaves):
            lines.append(f"int __cov_d{info.id}_c{index} = !!({self.visit(leaf)}); ")
        lines.append(f"int __cov_d{info.id}_result = !!({rebuilt_expression(condition)}); ")
        values = ", ".join(f"__cov_d{info.id}_c{index}" for index in range(len(leaves)))
        lines.append(f"int __cov_d{info.id}_values[{max(1, len(leaves))}] = {{{values}}}; ")
        lines.append(
            f"__cov_record_decision({info.id}, __cov_d{info.id}_result, "
            f"{len(leaves)}, __cov_d{info.id}_values); "
        )
        lines.append(f"__cov_d{info.id}_result; }})")
        return "".join(lines)


def strip_comments_and_preprocessor(source: str) -> str:
    out: list[str] = []
    i = 0
    state = "normal"

    while i < len(source):
        ch = source[i]
        nxt = source[i + 1] if i + 1 < len(source) else ""

        if state == "normal":
            if ch == "/" and nxt == "/":
                out.extend("  ")
                i += 2
                state = "line_comment"
                continue
            if ch == "/" and nxt == "*":
                out.extend("  ")
                i += 2
                state = "block_comment"
                continue
            if ch == '"':
                out.append(ch)
                i += 1
                state = "string"
                continue
            if ch == "'":
                out.append(ch)
                i += 1
                state = "char"
                continue
            out.append(ch)
            i += 1
            continue

        if state == "line_comment":
            if ch == "\n":
                out.append(ch)
                state = "normal"
            else:
                out.append(" ")
            i += 1
            continue

        if state == "block_comment":
            if ch == "*" and nxt == "/":
                out.extend("  ")
                i += 2
                state = "normal"
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if state in ("string", "char"):
            out.append(ch)
            if ch == "\\" and i + 1 < len(source):
                out.append(source[i + 1])
                i += 2
                continue
            if (state == "string" and ch == '"') or (state == "char" and ch == "'"):
                state = "normal"
            i += 1
            continue

    without_comments = "".join(out)
    sanitized_lines = []
    for line in without_comments.splitlines(keepends=True):
        if line.lstrip().startswith("#"):
            sanitized_lines.append("\n" if line.endswith("\n") else "")
        else:
            sanitized_lines.append(line)
    return "".join(sanitized_lines)


def parse_c_file(path: Path) -> tuple[str, c_ast.FileAST, c_ast.FuncDef]:
    source = path.read_text(encoding="utf-8")
    sanitized = strip_comments_and_preprocessor(source)
    parser = c_parser.CParser()
    try:
        ast = parser.parse(PARSER_PREFIX + sanitized, filename=str(path))
    except Exception as exc:
        raise SystemExit(f"Could not parse {path}: {exc}") from exc

    functions = [node for _, node in ast.children() if isinstance(node, c_ast.FuncDef)]
    if len(functions) != 1:
        raise SystemExit(f"Expected exactly one function definition, found {len(functions)}.")
    return source, ast, functions[0]


def function_parameters(function: c_ast.FuncDef) -> list[ParameterInfo]:
    generator = c_generator.CGenerator()
    args = function.decl.type.args
    if args is None:
        return []

    params: list[ParameterInfo] = []
    for index, param in enumerate(args.params):
        if isinstance(param, c_ast.EllipsisParam):
            raise SystemExit("Variadic functions are not supported.")
        if not isinstance(param, c_ast.Decl):
            continue
        type_name = normalize_type_name(generator._generate_type(param.type, emit_declname=False))
        if type_name == "void" and len(args.params) == 1:
            return []
        if "*" in type_name or "[" in type_name or "]" in type_name:
            raise SystemExit(f"Parameter {param.name or index} has non-primitive type {type_name!r}.")
        params.append(ParameterInfo(name=param.name or f"arg{index}", type_name=type_name))
    if not (0 <= len(params) <= 5):
        raise SystemExit(f"Expected between 0 and 5 parameters, found {len(params)}.")
    return params


def normalize_type_name(type_name: str) -> str:
    return " ".join(type_name.replace("\n", " ").split())


def load_cases(path: Path, parameters: list[ParameterInfo]) -> list[list[Any]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SystemExit(f"Cases file does not exist: {path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Invalid JSON in {path}: {exc}") from exc

    if isinstance(data, dict):
        raw_cases = data.get("cases")
    else:
        raw_cases = data

    if not isinstance(raw_cases, list):
        raise SystemExit("Cases must be a JSON list, or an object with a 'cases' list.")

    cases: list[list[Any]] = []
    for case_index, case in enumerate(raw_cases):
        if isinstance(case, dict):
            try:
                values = [case[param.name] for param in parameters]
            except KeyError as exc:
                raise SystemExit(f"Case {case_index} is missing parameter {exc.args[0]!r}.") from exc
        elif len(parameters) == 1 and not isinstance(case, list):
            values = [case]
        elif isinstance(case, list):
            values = case
        else:
            raise SystemExit(f"Case {case_index} must be a list or object.")

        if len(values) != len(parameters):
            raise SystemExit(
                f"Case {case_index} has {len(values)} values, but the function takes {len(parameters)} parameters."
            )
        cases.append(values)

    return cases


def value_to_c_literal(value: Any, type_name: str) -> str:
    if isinstance(value, dict):
        if "$c" in value:
            return str(value["$c"])
        raise SystemExit(f"Unsupported value object {value!r}; use {{\"$c\": \"C_LITERAL\"}} for raw C.")

    normalized = normalize_type_name(type_name).lower()
    if normalized in ("bool", "_bool"):
        if isinstance(value, bool):
            return "true" if value else "false"
        if isinstance(value, str) and value.lower() in ("true", "false", "0", "1"):
            return "true" if value.lower() in ("true", "1") else "false"

    if isinstance(value, bool):
        return "true" if value else "false"

    if isinstance(value, int):
        return str(value)

    if isinstance(value, float):
        return repr(value)

    if isinstance(value, str):
        if normalized in ("char", "signed char", "unsigned char") and len(value) == 1:
            return "'" + escape_c_char(value) + "'"
        return value

    raise SystemExit(f"Unsupported case value {value!r} for type {type_name!r}.")


def escape_c_char(value: str) -> str:
    escapes = {
        "\\": "\\\\",
        "'": "\\'",
        "\n": "\\n",
        "\r": "\\r",
        "\t": "\\t",
        "\0": "\\0",
    }
    return escapes.get(value, value)


def function_name(function: c_ast.FuncDef) -> str:
    return function.decl.name


def generate_runtime_header(statement_count: int, decision_count: int, max_conditions: int, max_observations: int) -> str:
    stmt_dim = max(1, statement_count)
    dec_dim = max(1, decision_count)
    cond_dim = max(1, max_conditions)
    return f"""\
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#define __COV_STATEMENTS {statement_count}
#define __COV_DECISIONS {decision_count}
#define __COV_MAX_CONDITIONS {cond_dim}
#define __COV_MAX_OBSERVATIONS {max_observations}

static unsigned char __cov_stmt_seen[{stmt_dim}];
static unsigned char __cov_decision_seen[{dec_dim}][2];
static unsigned char __cov_condition_seen[{dec_dim}][{cond_dim}][2];
static unsigned char __cov_observation_values[{dec_dim}][__COV_MAX_OBSERVATIONS][{cond_dim}];
static unsigned char __cov_observation_result[{dec_dim}][__COV_MAX_OBSERVATIONS];
static int __cov_observation_count[{dec_dim}];
static unsigned char __cov_observation_overflow[{dec_dim}];

static void __cov_stmt(int id) {{
    if (id >= 0 && id < __COV_STATEMENTS) {{
        __cov_stmt_seen[id] = 1;
    }}
}}

static void __cov_record_decision(int id, int result, int condition_count, const int *values) {{
    int normalized_result = !!result;
    int i;
    if (id < 0 || id >= __COV_DECISIONS) {{
        return;
    }}

    __cov_decision_seen[id][normalized_result] = 1;
    for (i = 0; i < condition_count && i < __COV_MAX_CONDITIONS; ++i) {{
        __cov_condition_seen[id][i][!!values[i]] = 1;
    }}

    if (__cov_observation_count[id] >= __COV_MAX_OBSERVATIONS) {{
        __cov_observation_overflow[id] = 1;
        return;
    }}

    __cov_observation_result[id][__cov_observation_count[id]] = (unsigned char)normalized_result;
    for (i = 0; i < condition_count && i < __COV_MAX_CONDITIONS; ++i) {{
        __cov_observation_values[id][__cov_observation_count[id]][i] = (unsigned char)(!!values[i]);
    }}
    ++__cov_observation_count[id];
}}

static void __cov_dump(void) {{
    int i;
    int j;
    int k;
    for (i = 0; i < __COV_STATEMENTS; ++i) {{
        printf("S %d %d\\n", i, __cov_stmt_seen[i] ? 1 : 0);
    }}
    for (i = 0; i < __COV_DECISIONS; ++i) {{
        printf("D %d %d %d\\n", i, __cov_decision_seen[i][0] ? 1 : 0, __cov_decision_seen[i][1] ? 1 : 0);
        for (j = 0; j < __COV_MAX_CONDITIONS; ++j) {{
            printf("C %d %d %d %d\\n", i, j, __cov_condition_seen[i][j][0] ? 1 : 0, __cov_condition_seen[i][j][1] ? 1 : 0);
        }}
        for (j = 0; j < __cov_observation_count[i]; ++j) {{
            printf("O %d %d ", i, __cov_observation_result[i][j] ? 1 : 0);
            for (k = 0; k < __COV_MAX_CONDITIONS; ++k) {{
                putchar(__cov_observation_values[i][j][k] ? '1' : '0');
            }}
            putchar('\\n');
        }}
        if (__cov_observation_overflow[i]) {{
            printf("X %d\\n", i);
        }}
    }}
}}
"""


def generate_harness(
    function: c_ast.FuncDef,
    analysis: CoverageAnalyzer,
    parameters: list[ParameterInfo],
    cases: list[list[Any]],
    max_observations: int,
) -> str:
    max_conditions = max((len(decision.conditions) for decision in analysis.decisions), default=1)
    runtime = generate_runtime_header(
        statement_count=len(analysis.statements),
        decision_count=len(analysis.decisions),
        max_conditions=max_conditions,
        max_observations=max_observations,
    )
    instrumented_function = InstrumentingGenerator(analysis).visit(function)
    calls = []
    name = function_name(function)
    for case in cases:
        args = []
        for value, parameter in zip(case, parameters):
            literal = value_to_c_literal(value, parameter.type_name)
            args.append(f"(({parameter.type_name})({literal}))")
        calls.append(f"    (void){name}({', '.join(args)});")
    if not calls:
        calls.append("    /* no cases supplied */")

    main = "\n".join(
        [
            "int main(void) {",
            *calls,
            "    __cov_dump();",
            "    return 0;",
            "}",
            "",
        ]
    )
    return runtime + "\n" + instrumented_function + "\n" + main


def compile_and_run(source: str, build_dir: Path, timeout: float) -> str:
    generated_c = build_dir / "instrumented.c"
    binary = build_dir / "coverage_harness"
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


@dataclass
class RuntimeData:
    statement_seen: dict[int, bool]
    decision_seen: dict[int, tuple[bool, bool]]
    condition_seen: dict[tuple[int, int], tuple[bool, bool]]
    observations: dict[int, list[tuple[int, str]]]
    overflow_decisions: set[int]


def parse_runtime_output(output: str) -> RuntimeData:
    statement_seen: dict[int, bool] = {}
    decision_seen: dict[int, tuple[bool, bool]] = {}
    condition_seen: dict[tuple[int, int], tuple[bool, bool]] = {}
    observations: dict[int, list[tuple[int, str]]] = {}
    overflow_decisions: set[int] = set()

    for raw_line in output.splitlines():
        parts = raw_line.split()
        if not parts:
            continue
        tag = parts[0]
        if tag == "S":
            statement_seen[int(parts[1])] = parts[2] == "1"
        elif tag == "D":
            decision_seen[int(parts[1])] = (parts[2] == "1", parts[3] == "1")
        elif tag == "C":
            condition_seen[(int(parts[1]), int(parts[2]))] = (parts[3] == "1", parts[4] == "1")
        elif tag == "O":
            observations.setdefault(int(parts[1]), []).append((int(parts[2]), parts[3]))
        elif tag == "X":
            overflow_decisions.add(int(parts[1]))

    return RuntimeData(
        statement_seen=statement_seen,
        decision_seen=decision_seen,
        condition_seen=condition_seen,
        observations=observations,
        overflow_decisions=overflow_decisions,
    )


def compute_mcdc(decision: DecisionInfo, observations: list[tuple[int, str]]) -> list[bool]:
    covered = [False] * len(decision.conditions)
    for left_index, (left_result, left_bits) in enumerate(observations):
        for right_result, right_bits in observations[left_index + 1 :]:
            if left_result == right_result:
                continue
            for condition_index in range(len(decision.conditions)):
                if covered[condition_index]:
                    continue
                if left_bits[condition_index] == right_bits[condition_index]:
                    continue
                others_same = all(
                    left_bits[index] == right_bits[index]
                    for index in range(len(decision.conditions))
                    if index != condition_index
                )
                if others_same:
                    covered[condition_index] = True
    return covered


def source_excerpt(source_lines: list[str], line: int) -> str:
    if 1 <= line <= len(source_lines):
        return source_lines[line - 1].strip()
    return ""


def line_key(line: int, detail: str) -> tuple[int, str]:
    return (line, detail)


def build_report(
    source: str,
    function: c_ast.FuncDef,
    parameters: list[ParameterInfo],
    cases: list[list[Any]],
    analysis: CoverageAnalyzer,
    runtime: RuntimeData,
) -> str:
    source_lines = source.splitlines()
    name = function_name(function)
    signature = ", ".join(f"{param.type_name} {param.name}" for param in parameters)
    if not signature:
        signature = "void"

    lines: list[str] = [
        f"Function: {name}({signature})",
        f"Cases: {len(cases)}",
        "",
    ]

    missing_statement_lines = sorted(
        {
            info.line
            for info in analysis.statements
            if not runtime.statement_seen.get(info.id, False)
        }
    )
    append_line_report(
        lines,
        "Statement coverage",
        missing_statement_lines,
        source_lines,
    )

    missing_decisions: list[tuple[int, str]] = []
    for decision in analysis.decisions:
        saw_false, saw_true = runtime.decision_seen.get(decision.id, (False, False))
        missing = []
        if not saw_false:
            missing.append("false")
        if not saw_true:
            missing.append("true")
        if missing:
            missing_decisions.append(
                line_key(
                    decision.line,
                    f"missing decision outcome(s): {', '.join(missing)}; decision `{decision.expression}`",
                )
            )
    append_detail_report(lines, "Decision coverage", missing_decisions, source_lines)

    missing_conditions: list[tuple[int, str]] = []
    for decision in analysis.decisions:
        for condition in decision.conditions:
            saw_false, saw_true = runtime.condition_seen.get((decision.id, condition.id), (False, False))
            missing = []
            if not saw_false:
                missing.append("false")
            if not saw_true:
                missing.append("true")
            if missing:
                missing_conditions.append(
                    line_key(
                        condition.line,
                        f"condition `{condition.expression}` missing value(s): {', '.join(missing)}",
                    )
                )
    append_detail_report(lines, "Condition coverage", missing_conditions, source_lines)

    missing_mcdc: list[tuple[int, str]] = []
    for decision in analysis.decisions:
        covered = compute_mcdc(decision, runtime.observations.get(decision.id, []))
        for condition, is_covered in zip(decision.conditions, covered):
            if not is_covered:
                missing_mcdc.append(
                    line_key(
                        condition.line,
                        f"condition `{condition.expression}` has no MC/DC independence pair in decision `{decision.expression}`",
                    )
                )
    append_detail_report(lines, "MC/DC coverage", missing_mcdc, source_lines)

    if runtime.overflow_decisions:
        lines.append("")
        lines.append("Warning: observation storage overflowed for decision id(s): " + ", ".join(map(str, sorted(runtime.overflow_decisions))))
        lines.append("Increase --max-observations if MC/DC results look incomplete.")

    return "\n".join(lines)


def append_line_report(lines: list[str], title: str, missing_lines: list[int], source_lines: list[str]) -> None:
    if not missing_lines:
        lines.append(f"{title}: covered")
        lines.append("")
        return
    lines.append(f"{title}: not covered")
    for line in missing_lines:
        excerpt = source_excerpt(source_lines, line)
        lines.append(f"  line {line}: {excerpt}")
    lines.append("")


def append_detail_report(lines: list[str], title: str, missing: list[tuple[int, str]], source_lines: list[str]) -> None:
    if not missing:
        lines.append(f"{title}: covered")
        lines.append("")
        return
    lines.append(f"{title}: not covered")
    for line, detail in sorted(set(missing)):
        excerpt = source_excerpt(source_lines, line)
        lines.append(f"  line {line}: {excerpt}")
        lines.append(f"    {detail}")
    lines.append("")


def build_json_report(
    source: str,
    function: c_ast.FuncDef,
    parameters: list[ParameterInfo],
    cases: list[list[Any]],
    analysis: CoverageAnalyzer,
    runtime: RuntimeData,
) -> dict[str, Any]:
    source_lines = source.splitlines()
    statement_missing = [
        {
            "line": info.line,
            "source": source_excerpt(source_lines, info.line),
        }
        for info in analysis.statements
        if not runtime.statement_seen.get(info.id, False)
    ]

    decision_missing = []
    for decision in analysis.decisions:
        saw_false, saw_true = runtime.decision_seen.get(decision.id, (False, False))
        missing = [name for name, seen in (("false", saw_false), ("true", saw_true)) if not seen]
        if missing:
            decision_missing.append(
                {
                    "line": decision.line,
                    "source": source_excerpt(source_lines, decision.line),
                    "decision": decision.expression,
                    "missing": missing,
                }
            )

    condition_missing = []
    for decision in analysis.decisions:
        for condition in decision.conditions:
            saw_false, saw_true = runtime.condition_seen.get((decision.id, condition.id), (False, False))
            missing = [name for name, seen in (("false", saw_false), ("true", saw_true)) if not seen]
            if missing:
                condition_missing.append(
                    {
                        "line": condition.line,
                        "source": source_excerpt(source_lines, condition.line),
                        "decision": decision.expression,
                        "condition": condition.expression,
                        "missing": missing,
                    }
                )

    mcdc_missing = []
    for decision in analysis.decisions:
        covered = compute_mcdc(decision, runtime.observations.get(decision.id, []))
        for condition, is_covered in zip(decision.conditions, covered):
            if not is_covered:
                mcdc_missing.append(
                    {
                        "line": condition.line,
                        "source": source_excerpt(source_lines, condition.line),
                        "decision": decision.expression,
                        "condition": condition.expression,
                    }
                )

    return {
        "function": function_name(function),
        "parameters": [param.__dict__ for param in parameters],
        "case_count": len(cases),
        "coverage": {
            "statement": {"covered": not statement_missing, "missing": statement_missing},
            "decision": {"covered": not decision_missing, "missing": decision_missing},
            "condition": {"covered": not condition_missing, "missing": condition_missing},
            "mcdc": {"covered": not mcdc_missing, "missing": mcdc_missing},
        },
        "overflow_decisions": sorted(runtime.overflow_decisions),
    }


def write_case_template(path: Path, parameters: list[ParameterInfo]) -> None:
    if len(parameters) == 1:
        cases: list[Any] = [0, 1]
    else:
        zero_case = [False if p.type_name.lower() in ("bool", "_bool") else 0 for p in parameters]
        one_case = [True if p.type_name.lower() in ("bool", "_bool") else 1 for p in parameters]
        cases = [zero_case, one_case]
    template = {
        "cases": cases,
        "_notes": [
            "Cases can be positional lists, or objects keyed by parameter name.",
            "Use {\"$c\": \"C_LITERAL\"} for raw C literals such as UINT_MAX or 42UL.",
        ],
    }
    path.write_text(json.dumps(template, indent=2) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check statement, decision, condition, and MC/DC coverage for one C function.")
    parser.add_argument("source", nargs="?", default="input.c", help="C file containing exactly one function. Default: input.c")
    parser.add_argument("cases", nargs="?", default="cases.json", help="JSON file with test cases. Default: cases.json")
    parser.add_argument("--json", action="store_true", help="Print machine-readable JSON instead of the text report.")
    parser.add_argument("--keep", action="store_true", help="Keep the generated instrumented C file and harness binary.")
    parser.add_argument("--init-cases", action="store_true", help="Write a starter cases file and exit.")
    parser.add_argument("--max-observations", type=int, default=100000, help="Max decision observations stored for MC/DC per decision.")
    parser.add_argument("--timeout", type=float, default=5.0, help="Timeout in seconds for running the instrumented program.")
    args = parser.parse_args(argv)

    source_path = Path(args.source)
    cases_path = Path(args.cases)
    source, _, function = parse_c_file(source_path)
    parameters = function_parameters(function)

    if args.init_cases:
        write_case_template(cases_path, parameters)
        print(f"Wrote {cases_path}")
        return 0

    cases = load_cases(cases_path, parameters)
    analysis = CoverageAnalyzer(line_offset=PARSER_PREFIX_LINES)
    analysis.analyze_function(function)

    harness = generate_harness(
        function=function,
        analysis=analysis,
        parameters=parameters,
        cases=cases,
        max_observations=max(1, args.max_observations),
    )

    if args.keep:
        build_dir = Path(".coverage_build")
        if build_dir.exists():
            shutil.rmtree(build_dir)
        build_dir.mkdir(parents=True)
        output = compile_and_run(harness, build_dir, timeout=args.timeout)
        kept_dir: Path | None = build_dir
    else:
        with tempfile.TemporaryDirectory(prefix="coverage_check_") as tmp:
            output = compile_and_run(harness, Path(tmp), timeout=args.timeout)
        kept_dir = None

    runtime = parse_runtime_output(output)
    if args.json:
        print(json.dumps(build_json_report(source, function, parameters, cases, analysis, runtime), indent=2))
    else:
        print(build_report(source, function, parameters, cases, analysis, runtime))
        if kept_dir is not None:
            print(f"Kept generated files in {kept_dir}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
