#!/usr/bin/env python3
"""Classify C loop-invariant candidates with Z3.

The tool expects one C function with one top-level while loop.  Statements before
that loop are treated as initialization; the candidate formula is checked at the
loop head.
"""

from __future__ import annotations

import argparse
import dataclasses
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Iterable

from pycparser import c_ast, c_generator, c_parser


class InvariantError(Exception):
    pass


@dataclasses.dataclass(frozen=True)
class Token:
    kind: str
    value: str
    line: int
    col: int


KEYWORDS = {
    "and",
    "candidate",
    "false",
    "invariant",
    "not",
    "or",
    "pre",
    "reachable",
    "true",
}


TOKEN_RE = re.compile(
    r"""
    (?P<space>[ \t\r\n]+)
  | (?P<line_comment>//[^\n]*|\#[^\n]*)
  | (?P<block_comment>/\*.*?\*/)
  | (?P<int>\d+)
  | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<op>==|!=|<=|>=|&&|\|\||=>|[{}();,+\-*/%<>=!])
    """,
    re.VERBOSE | re.DOTALL,
)


def tokenize(text: str) -> list[Token]:
    tokens: list[Token] = []
    line = 1
    col = 1
    pos = 0
    for match in TOKEN_RE.finditer(text):
        if match.start() != pos:
            snippet = text[pos : match.start()]
            raise InvariantError(f"unexpected text at {line}:{col}: {snippet!r}")

        value = match.group(0)
        kind = match.lastgroup or ""
        start_line = line
        start_col = col
        newlines = value.count("\n")
        if newlines:
            line += newlines
            col = len(value.rsplit("\n", 1)[-1]) + 1
        else:
            col += len(value)
        pos = match.end()

        if kind in {"space", "line_comment", "block_comment"}:
            continue
        if kind == "id" and value in KEYWORDS:
            tokens.append(Token(value, value, start_line, start_col))
        elif kind == "id":
            tokens.append(Token("id", value, start_line, start_col))
        elif kind == "int":
            tokens.append(Token("int_lit", value, start_line, start_col))
        else:
            tokens.append(Token(value, value, start_line, start_col))

    if pos != len(text):
        snippet = text[pos:]
        raise InvariantError(f"unexpected text at {line}:{col}: {snippet!r}")
    tokens.append(Token("eof", "", line, col))
    return tokens


@dataclasses.dataclass(frozen=True)
class Expr:
    def subst(self, name: str, replacement: "Expr") -> "Expr":
        return self

    def variables(self) -> set[str]:
        return set()

    def to_source(self) -> str:
        raise NotImplementedError

    def to_smt(self) -> str:
        raise NotImplementedError


@dataclasses.dataclass(frozen=True)
class IntLit(Expr):
    value: int

    def to_source(self) -> str:
        return str(self.value)

    def to_smt(self) -> str:
        if self.value < 0:
            return f"(- {abs(self.value)})"
        return str(self.value)


@dataclasses.dataclass(frozen=True)
class BoolLit(Expr):
    value: bool

    def to_source(self) -> str:
        return "true" if self.value else "false"

    def to_smt(self) -> str:
        return "true" if self.value else "false"


@dataclasses.dataclass(frozen=True)
class Var(Expr):
    name: str

    def subst(self, name: str, replacement: Expr) -> Expr:
        if self.name == name:
            return replacement
        return self

    def variables(self) -> set[str]:
        return {self.name}

    def to_source(self) -> str:
        return self.name

    def to_smt(self) -> str:
        return smt_name(self.name)


@dataclasses.dataclass(frozen=True)
class Unary(Expr):
    op: str
    expr: Expr

    def subst(self, name: str, replacement: Expr) -> Expr:
        return Unary(self.op, self.expr.subst(name, replacement))

    def variables(self) -> set[str]:
        return self.expr.variables()

    def to_source(self) -> str:
        return f"{self.op}{wrap_source(self.expr)}"

    def to_smt(self) -> str:
        if self.op == "-":
            return f"(- {self.expr.to_smt()})"
        if self.op == "!":
            return f"(not {self.expr.to_smt()})"
        raise InvariantError(f"unknown unary operator {self.op}")


@dataclasses.dataclass(frozen=True)
class Binary(Expr):
    op: str
    left: Expr
    right: Expr

    def subst(self, name: str, replacement: Expr) -> Expr:
        return Binary(self.op, self.left.subst(name, replacement), self.right.subst(name, replacement))

    def variables(self) -> set[str]:
        return self.left.variables() | self.right.variables()

    def to_source(self) -> str:
        return f"({self.left.to_source()} {self.op} {self.right.to_source()})"

    def to_smt(self) -> str:
        left = self.left.to_smt()
        right = self.right.to_smt()
        if self.op in {"+", "-", "*", "<", "<=", ">", ">=", "="}:
            return f"({self.op} {left} {right})"
        if self.op == "/":
            return f"(div {left} {right})"
        if self.op == "%":
            return f"(mod {left} {right})"
        if self.op == "&&":
            return f"(and {left} {right})"
        if self.op == "||":
            return f"(or {left} {right})"
        if self.op == "=>":
            return f"(=> {left} {right})"
        if self.op == "==":
            return f"(= {left} {right})"
        if self.op == "!=":
            return f"(not (= {left} {right}))"
        raise InvariantError(f"unknown binary operator {self.op}")


@dataclasses.dataclass(frozen=True)
class Ite(Expr):
    cond: Expr
    then_expr: Expr
    else_expr: Expr

    def subst(self, name: str, replacement: Expr) -> Expr:
        return Ite(
            self.cond.subst(name, replacement),
            self.then_expr.subst(name, replacement),
            self.else_expr.subst(name, replacement),
        )

    def variables(self) -> set[str]:
        return self.cond.variables() | self.then_expr.variables() | self.else_expr.variables()

    def to_source(self) -> str:
        return (
            f"(if {self.cond.to_source()} then "
            f"{self.then_expr.to_source()} else {self.else_expr.to_source()})"
        )

    def to_smt(self) -> str:
        return f"(ite {self.cond.to_smt()} {self.then_expr.to_smt()} {self.else_expr.to_smt()})"


def wrap_source(expr: Expr) -> str:
    if isinstance(expr, (IntLit, BoolLit, Var)):
        return expr.to_source()
    return f"({expr.to_source()})"


def smt_name(name: str) -> str:
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        return name
    escaped = name.replace("|", "||")
    return f"|{escaped}|"


def mk_and(parts: Iterable[Expr]) -> Expr:
    items = [part for part in parts if not (isinstance(part, BoolLit) and part.value)]
    if not items:
        return BoolLit(True)
    expr = items[0]
    for item in items[1:]:
        expr = Binary("&&", expr, item)
    return expr


def mk_not(expr: Expr) -> Expr:
    if isinstance(expr, BoolLit):
        return BoolLit(not expr.value)
    return Unary("!", expr)


def mk_implies(left: Expr, right: Expr) -> Expr:
    return Binary("=>", left, right)


@dataclasses.dataclass(frozen=True)
class Stmt:
    line: int

    def variables(self) -> set[str]:
        return set()


@dataclasses.dataclass(frozen=True)
class Skip(Stmt):
    pass


@dataclasses.dataclass(frozen=True)
class Assign(Stmt):
    name: str
    expr: Expr

    def variables(self) -> set[str]:
        return {self.name} | self.expr.variables()


@dataclasses.dataclass(frozen=True)
class If(Stmt):
    cond: Expr
    then_body: list[Stmt]
    else_body: list[Stmt]

    def variables(self) -> set[str]:
        names = set(self.cond.variables())
        for stmt in self.then_body + self.else_body:
            names |= stmt.variables()
        return names


class FormulaParser:
    def __init__(self, tokens: list[Token], path: Path):
        self.tokens = tokens
        self.i = 0
        self.path = path

    def current(self) -> Token:
        return self.tokens[self.i]

    def at(self, kind: str) -> bool:
        return self.current().kind == kind

    def match(self, kind: str) -> Token | None:
        if self.at(kind):
            token = self.current()
            self.i += 1
            return token
        return None

    def expect(self, kind: str) -> Token:
        token = self.match(kind)
        if token is not None:
            return token
        cur = self.current()
        raise InvariantError(
            f"{self.path}:{cur.line}:{cur.col}: expected {kind!r}, got {cur.kind!r}"
        )

    def parse_braced_expr(self) -> Expr:
        self.expect("{")
        expr = self.parse_expr()
        # Be forgiving for worksheet-style inputs such as `{(p)=>(q))}` where
        # the whole implication was meant to be parenthesized.
        while self.at(")") and self.tokens[self.i + 1].kind == "}":
            self.expect(")")
        self.expect("}")
        return expr

    def parse_expr(self) -> Expr:
        return self.parse_implies()

    def parse_implies(self) -> Expr:
        left = self.parse_or()
        if self.match("=>"):
            right = self.parse_implies()
            return Binary("=>", left, right)
        return left

    def parse_or(self) -> Expr:
        expr = self.parse_and()
        while self.match("||") or self.match("or"):
            expr = Binary("||", expr, self.parse_and())
        return expr

    def parse_and(self) -> Expr:
        expr = self.parse_equality()
        while self.match("&&") or self.match("and"):
            expr = Binary("&&", expr, self.parse_equality())
        return expr

    def parse_equality(self) -> Expr:
        expr = self.parse_relation()
        while True:
            if self.match("=="):
                expr = Binary("==", expr, self.parse_relation())
            elif self.match("="):
                expr = Binary("==", expr, self.parse_relation())
            elif self.match("!="):
                expr = Binary("!=", expr, self.parse_relation())
            else:
                return expr

    def parse_relation(self) -> Expr:
        expr = self.parse_add()
        while True:
            if self.match("<="):
                expr = Binary("<=", expr, self.parse_add())
            elif self.match(">="):
                expr = Binary(">=", expr, self.parse_add())
            elif self.match("<"):
                expr = Binary("<", expr, self.parse_add())
            elif self.match(">"):
                expr = Binary(">", expr, self.parse_add())
            else:
                return expr

    def parse_add(self) -> Expr:
        expr = self.parse_mul()
        while True:
            if self.match("+"):
                expr = Binary("+", expr, self.parse_mul())
            elif self.match("-"):
                expr = Binary("-", expr, self.parse_mul())
            else:
                return expr

    def parse_mul(self) -> Expr:
        expr = self.parse_unary()
        while True:
            if self.match("*"):
                expr = Binary("*", expr, self.parse_unary())
            elif self.match("/"):
                expr = Binary("/", expr, self.parse_unary())
            elif self.match("%"):
                expr = Binary("%", expr, self.parse_unary())
            else:
                return expr

    def parse_unary(self) -> Expr:
        if self.match("!"):
            return Unary("!", self.parse_unary())
        if self.match("not"):
            return Unary("!", self.parse_unary())
        if self.match("-"):
            return Unary("-", self.parse_unary())
        return self.parse_primary()

    def parse_primary(self) -> Expr:
        if token := self.match("int_lit"):
            return IntLit(int(token.value))
        if self.match("true"):
            return BoolLit(True)
        if self.match("false"):
            return BoolLit(False)
        if token := self.match("id"):
            return Var(token.value)
        if self.match("("):
            expr = self.parse_expr()
            self.expect(")")
            return expr
        cur = self.current()
        raise InvariantError(f"{self.path}:{cur.line}:{cur.col}: expected expression")


@dataclasses.dataclass
class FormulaInput:
    pre: Expr
    candidates: list[Expr]
    reachable: Expr | None


class FormulaFileParser(FormulaParser):
    def parse_file(self) -> FormulaInput:
        pre: Expr | None = None
        reachable_parts: list[Expr] = []
        candidates: list[Expr] = []

        directive_mode = any(
            token.kind in {"pre", "reachable", "candidate", "invariant"}
            for token in self.tokens
        )

        if directive_mode:
            while not self.at("eof"):
                if self.match("pre"):
                    pre = self.parse_braced_expr()
                elif self.match("reachable"):
                    reachable_parts.append(self.parse_braced_expr())
                elif self.match("candidate") or self.match("invariant"):
                    candidates.append(self.parse_braced_expr())
                elif self.at("{"):
                    candidates.append(self.parse_braced_expr())
                else:
                    cur = self.current()
                    raise InvariantError(
                        f"{self.path}:{cur.line}:{cur.col}: "
                        "expected 'pre', 'reachable', 'candidate', 'invariant', or '{'"
                    )
                self.match(";")
        else:
            while not self.at("eof"):
                if self.at("{"):
                    candidates.append(self.parse_braced_expr())
                    self.match(";")
                else:
                    candidates.append(self.parse_expr())
                    self.expect("eof")
                    break

        if not candidates:
            raise InvariantError(f"{self.path}: expected at least one candidate formula")
        return FormulaInput(pre or BoolLit(True), candidates, mk_and(reachable_parts) if reachable_parts else None)


def parse_formula_file(path: Path) -> FormulaInput:
    return FormulaFileParser(tokenize(path.read_text(encoding="utf-8")), path).parse_file()


PARSER_PREFIX = """\
typedef _Bool bool;
typedef unsigned char uint8_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;
typedef unsigned long size_t;
"""


@dataclasses.dataclass(frozen=True)
class Parameter:
    name: str
    typ: str


@dataclasses.dataclass
class CLoopProblem:
    path: Path
    function_name: str
    parameters: list[Parameter]
    types: dict[str, str]
    init: list[Stmt]
    guard: Expr
    body: list[Stmt]


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
        if state in {"string", "char"}:
            out.append(ch)
            if ch == "\\" and i + 1 < len(source):
                out.append(source[i + 1])
                i += 2
                continue
            if (state == "string" and ch == '"') or (state == "char" and ch == "'"):
                state = "normal"
            i += 1
    sanitized_lines = []
    for line in "".join(out).splitlines(keepends=True):
        sanitized_lines.append("\n" if line.lstrip().startswith("#") else line)
    return "".join(sanitized_lines)


def parse_c_file(path: Path) -> c_ast.FuncDef:
    source = path.read_text(encoding="utf-8")
    parser = c_parser.CParser()
    try:
        ast = parser.parse(PARSER_PREFIX + strip_comments_and_preprocessor(source), filename=str(path))
    except Exception as exc:
        raise InvariantError(f"could not parse {path}: {exc}") from exc

    functions = [node for _, node in ast.children() if isinstance(node, c_ast.FuncDef)]
    if len(functions) != 1:
        raise InvariantError(f"expected exactly one function definition, found {len(functions)}")
    return functions[0]


def normalize_type_name(type_name: str) -> str:
    return " ".join(type_name.replace("\n", " ").split())


def c_type_name(node: c_ast.Node) -> str:
    generator = c_generator.CGenerator()
    return normalize_type_name(generator._generate_type(node, emit_declname=False))


def invariant_type_from_c(type_name: str) -> str:
    normalized = normalize_type_name(type_name).lower()
    if "*" in normalized or "[" in normalized or "]" in normalized:
        raise InvariantError(f"unsupported non-scalar type {type_name!r}")
    if normalized in {"bool", "_bool"}:
        return "Bool"
    if any(word in normalized for word in ("float", "double")):
        raise InvariantError(f"floating-point type {type_name!r} is not supported")
    if "unsigned" in normalized or normalized.startswith("uint") or normalized == "size_t":
        return "Nat"
    if any(word in normalized for word in ("char", "short", "int", "long", "signed")):
        return "Int"
    raise InvariantError(f"unsupported type {type_name!r}")


def function_parameters(function: c_ast.FuncDef) -> list[Parameter]:
    args = function.decl.type.args
    if args is None:
        return []
    params: list[Parameter] = []
    for index, param in enumerate(args.params):
        if isinstance(param, c_ast.EllipsisParam):
            raise InvariantError("variadic functions are not supported")
        if not isinstance(param, c_ast.Decl):
            continue
        type_name = c_type_name(param.type)
        if normalize_type_name(type_name).lower() == "void" and len(args.params) == 1:
            return []
        params.append(Parameter(param.name or f"arg{index}", invariant_type_from_c(type_name)))
    return params


def is_variable_decl(node: c_ast.Node) -> bool:
    return isinstance(node, c_ast.Decl) and not isinstance(node.type, c_ast.FuncDecl)


def collect_local_types(node: c_ast.Node, types: dict[str, str]) -> None:
    if is_variable_decl(node):
        assert isinstance(node, c_ast.Decl)
        if node.name in types:
            raise InvariantError(f"duplicate or shadowed variable {node.name!r} is not supported")
        types[node.name] = invariant_type_from_c(c_type_name(node.type))
    for _, child in node.children():
        collect_local_types(child, types)


def parse_c_problem(path: Path) -> CLoopProblem:
    function = parse_c_file(path)
    parameters = function_parameters(function)
    types = {param.name: param.typ for param in parameters}
    collect_local_types(function.body, types)

    items = list(function.body.block_items or [])
    while_indexes = [index for index, item in enumerate(items) if isinstance(item, c_ast.While)]
    if len(while_indexes) != 1:
        raise InvariantError(
            f"{path}: expected exactly one top-level while loop, found {len(while_indexes)}"
        )
    while_index = while_indexes[0]
    while_node = items[while_index]
    assert isinstance(while_node, c_ast.While)

    init = parse_statement_list(items[:while_index])
    body = parse_statement_as_block(while_node.stmt)
    return CLoopProblem(
        path=path,
        function_name=function.decl.name,
        parameters=parameters,
        types=types,
        init=init,
        guard=c_expr(while_node.cond),
        body=body,
    )


def parse_statement_list(nodes: Iterable[c_ast.Node]) -> list[Stmt]:
    stmts: list[Stmt] = []
    for node in nodes:
        stmts.extend(parse_statement(node))
    return stmts


def parse_statement_as_block(node: c_ast.Node | None) -> list[Stmt]:
    if node is None:
        return []
    if isinstance(node, c_ast.Compound):
        return parse_statement_list(node.block_items or [])
    return parse_statement(node)


def node_line(node: c_ast.Node | None) -> int:
    coord = getattr(node, "coord", None)
    return int(coord.line) if coord is not None and coord.line is not None else 0


def parse_statement(node: c_ast.Node) -> list[Stmt]:
    line = node_line(node)
    if isinstance(node, c_ast.EmptyStatement):
        return []
    if isinstance(node, c_ast.Compound):
        return parse_statement_as_block(node)
    if isinstance(node, c_ast.Decl):
        if node.init is None:
            return [Skip(line)]
        return [Assign(line, node.name, c_expr(node.init))]
    if isinstance(node, c_ast.Assignment):
        return [assignment_stmt(line, node)]
    if isinstance(node, c_ast.If):
        return [
            If(
                line,
                c_expr(node.cond),
                parse_statement_as_block(node.iftrue),
                parse_statement_as_block(node.iffalse),
            )
        ]
    if isinstance(node, c_ast.While):
        raise InvariantError(f"nested while loop at line {line} is not supported")
    if isinstance(node, c_ast.Return):
        raise InvariantError(f"return before the target loop at line {line} is not supported")
    if isinstance(node, c_ast.UnaryOp) and node.op in {"p++", "++", "p--", "--"}:
        if not isinstance(node.expr, c_ast.ID):
            raise InvariantError(f"unsupported increment expression at line {line}")
        delta = 1 if node.op in {"p++", "++"} else -1
        return [Assign(line, node.expr.name, Binary("+", Var(node.expr.name), IntLit(delta)))]
    raise InvariantError(f"unsupported C statement {node.__class__.__name__} at line {line}")


def assignment_stmt(line: int, node: c_ast.Assignment) -> Assign:
    if not isinstance(node.lvalue, c_ast.ID):
        raise InvariantError(f"unsupported assignment target at line {line}")
    name = node.lvalue.name
    if node.op == "=":
        expr = c_expr(node.rvalue)
    elif node.op in {"+=", "-=", "*=", "/=", "%="}:
        expr = Binary(node.op[0], Var(name), c_expr(node.rvalue))
    else:
        raise InvariantError(f"unsupported assignment operator {node.op!r} at line {line}")
    return Assign(line, name, expr)


def c_expr(node: c_ast.Node | None) -> Expr:
    if node is None:
        return BoolLit(True)
    if isinstance(node, c_ast.Constant):
        if node.type in {"int", "long", "long long", "unsigned int", "unsigned long"}:
            return IntLit(int(re.sub(r"[uUlL]+$", "", node.value), 0))
        raise InvariantError(f"unsupported C constant {node.value!r}")
    if isinstance(node, c_ast.ID):
        if node.name == "true":
            return BoolLit(True)
        if node.name == "false":
            return BoolLit(False)
        return Var(node.name)
    if isinstance(node, c_ast.BinaryOp):
        if node.op not in {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "||"}:
            raise InvariantError(f"unsupported C binary operator {node.op!r}")
        return Binary(node.op, c_expr(node.left), c_expr(node.right))
    if isinstance(node, c_ast.UnaryOp):
        if node.op == "!":
            return Unary("!", c_expr(node.expr))
        if node.op == "-":
            return Unary("-", c_expr(node.expr))
        if node.op == "+":
            return c_expr(node.expr)
        raise InvariantError(f"unsupported C unary operator {node.op!r}")
    if isinstance(node, c_ast.Cast):
        return c_expr(node.expr)
    if isinstance(node, c_ast.TernaryOp):
        return Ite(c_expr(node.cond), c_expr(node.iftrue), c_expr(node.iffalse))
    raise InvariantError(f"unsupported C expression {node.__class__.__name__}")


def subst_map(expr: Expr, state: dict[str, Expr]) -> Expr:
    if isinstance(expr, Var):
        return state.get(expr.name, expr)
    if isinstance(expr, (IntLit, BoolLit)):
        return expr
    if isinstance(expr, Unary):
        return Unary(expr.op, subst_map(expr.expr, state))
    if isinstance(expr, Binary):
        return Binary(expr.op, subst_map(expr.left, state), subst_map(expr.right, state))
    if isinstance(expr, Ite):
        return Ite(
            subst_map(expr.cond, state),
            subst_map(expr.then_expr, state),
            subst_map(expr.else_expr, state),
        )
    raise InvariantError(f"unsupported expression {expr!r}")


def symbolic_execute(stmts: list[Stmt], state: dict[str, Expr], variables: list[str]) -> dict[str, Expr]:
    current = dict(state)
    for stmt in stmts:
        current = symbolic_stmt(stmt, current, variables)
    return current


def symbolic_stmt(stmt: Stmt, state: dict[str, Expr], variables: list[str]) -> dict[str, Expr]:
    if isinstance(stmt, Skip):
        return dict(state)
    if isinstance(stmt, Assign):
        new_state = dict(state)
        new_state[stmt.name] = subst_map(stmt.expr, state)
        return new_state
    if isinstance(stmt, If):
        cond = subst_map(stmt.cond, state)
        then_state = symbolic_execute(stmt.then_body, dict(state), variables)
        else_state = symbolic_execute(stmt.else_body, dict(state), variables)
        merged: dict[str, Expr] = {}
        for name in variables:
            left = then_state.get(name, state.get(name, Var(name)))
            right = else_state.get(name, state.get(name, Var(name)))
            merged[name] = left if left == right else Ite(cond, left, right)
        return merged
    raise InvariantError(f"unsupported symbolic statement {stmt!r}")


def smt_types(types: dict[str, str]) -> dict[str, str]:
    return {name: ("Int" if typ == "Nat" else typ) for name, typ in types.items()}


def declarations_smt(types: dict[str, str]) -> str:
    return "\n".join(
        f"(declare-const {smt_name(name)} {typ})"
        for name, typ in sorted(smt_types(types).items())
    )


def domain_expr(types: dict[str, str], state: dict[str, Expr] | None = None) -> Expr:
    parts: list[Expr] = []
    for name, typ in sorted(types.items()):
        if typ == "Nat":
            term = state[name] if state and name in state else Var(name)
            parts.append(Binary(">=", term, IntLit(0)))
    return mk_and(parts)


def implication(antecedent: Expr, consequent: Expr) -> Expr:
    return mk_implies(antecedent, consequent)


def initialized_vc(problem: CLoopProblem, formula_input: FormulaInput, formula: Expr) -> Expr:
    variables = sorted(problem.types)
    init_state = symbolic_execute(problem.init, {name: Var(name) for name in variables}, variables)
    formula_at_loop = subst_map(formula, init_state)
    return implication(mk_and([domain_expr(problem.types), formula_input.pre]), formula_at_loop)


def preservation_vc(problem: CLoopProblem, formula: Expr) -> Expr:
    variables = sorted(problem.types)
    before_state = {name: Var(name) for name in variables}
    after_state = symbolic_execute(problem.body, before_state, variables)
    after_formula = subst_map(formula, after_state)
    return implication(mk_and([domain_expr(problem.types), formula, problem.guard]), after_formula)


@dataclasses.dataclass
class SolverResult:
    status: str
    raw: str = ""
    values: dict[str, str] = dataclasses.field(default_factory=dict)


def run_z3_script(script: str, z3_path: str, timeout: float) -> SolverResult:
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
        fh.write(script)
        smt_path = fh.name
    try:
        result = subprocess.run(
            [z3_path, "-smt2", smt_path],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return SolverResult("timeout")
    finally:
        Path(smt_path).unlink(missing_ok=True)

    raw = (result.stdout + result.stderr).strip()
    first_line = result.stdout.strip().splitlines()[0] if result.stdout.strip() else ""
    if first_line in {"sat", "unsat", "unknown"}:
        return SolverResult(first_line, raw=raw)
    return SolverResult("error", raw=raw)


def check_valid(expr: Expr, types: dict[str, str], z3_path: str, timeout: float) -> SolverResult:
    script = "\n".join(
        part
        for part in [
            "(set-option :produce-models true)",
            declarations_smt(types),
            f"(assert (not {expr.to_smt()}))",
            "(check-sat)",
        ]
        if part
    ) + "\n"
    result = run_z3_script(script, z3_path, timeout)
    if result.status == "unsat":
        return SolverResult("valid", raw=result.raw)
    if result.status == "sat":
        return SolverResult("invalid", raw=result.raw)
    return result


def sexpr_tokens(text: str) -> list[str]:
    return re.findall(r"\(|\)|[^\s()]+", text)


def parse_one_sexpr(tokens: list[str], pos: int = 0) -> tuple[object, int]:
    if pos >= len(tokens):
        raise InvariantError("unexpected end of S-expression")
    token = tokens[pos]
    if token != "(":
        return token, pos + 1
    pos += 1
    items: list[object] = []
    while pos < len(tokens) and tokens[pos] != ")":
        item, pos = parse_one_sexpr(tokens, pos)
        items.append(item)
    if pos >= len(tokens):
        raise InvariantError("unterminated S-expression")
    return items, pos + 1


def sexpr_to_text(value: object) -> str:
    if isinstance(value, str):
        return value
    if (
        isinstance(value, list)
        and len(value) == 2
        and value[0] == "-"
        and isinstance(value[1], str)
    ):
        return f"-{value[1]}"
    if isinstance(value, list):
        return "(" + " ".join(sexpr_to_text(item) for item in value) + ")"
    return str(value)


def parse_get_value_output(raw: str) -> dict[str, str]:
    lines = raw.splitlines()
    if not lines or lines[0].strip() != "sat":
        return {}
    text = "\n".join(lines[1:]).strip()
    if not text:
        return {}
    parsed, _ = parse_one_sexpr(sexpr_tokens(text))
    values: dict[str, str] = {}
    if isinstance(parsed, list):
        for pair in parsed:
            if isinstance(pair, list) and len(pair) == 2 and isinstance(pair[0], str):
                values[pair[0]] = sexpr_to_text(pair[1])
    return values


ValueTerm = tuple[str, str, Expr]


def check_sat_with_values(
    condition: Expr,
    types: dict[str, str],
    value_exprs: list[ValueTerm],
    z3_path: str,
    timeout: float,
) -> SolverResult:
    return check_sat_smt_with_values(condition.to_smt(), types, value_exprs, z3_path, timeout)


def check_sat_smt_with_values(
    condition_smt: str,
    types: dict[str, str],
    value_exprs: list[ValueTerm],
    z3_path: str,
    timeout: float,
    extra_declarations: list[str] | None = None,
) -> SolverResult:
    alias_decls: list[str] = []
    alias_asserts: list[str] = []
    value_names: list[str] = []
    for label, typ, expr in value_exprs:
        alias = f"__show_{label}"
        value_names.append(alias)
        alias_sort = "Int" if typ == "Nat" else typ
        alias_decls.append(f"(declare-const {smt_name(alias)} {alias_sort})")
        alias_asserts.append(f"(assert (= {smt_name(alias)} {expr.to_smt()}))")

    script = "\n".join(
        part
        for part in [
            "(set-option :produce-models true)",
            declarations_smt(types),
            *(extra_declarations or []),
            f"(assert {condition_smt})",
            *alias_decls,
            *alias_asserts,
            "(check-sat)",
            f"(get-value ({' '.join(smt_name(name) for name in value_names)}))"
            if value_names
            else "",
        ]
        if part
    ) + "\n"
    result = run_z3_script(script, z3_path, timeout)
    if result.status == "sat":
        result.values = {
            name.removeprefix("__show_"): value
            for name, value in parse_get_value_output(result.raw).items()
        }
    return result


def sorted_variables(types: dict[str, str]) -> list[str]:
    return sorted(types)


def statement_variables(stmts: list[Stmt]) -> set[str]:
    names: set[str] = set()
    for stmt in stmts:
        names |= stmt.variables()
    return names


def displayed_variables(problem: CLoopProblem, formula_input: FormulaInput) -> list[str]:
    names = set(problem.guard.variables()) | statement_variables(problem.body)
    for candidate in formula_input.candidates:
        names |= candidate.variables()
    if formula_input.reachable is not None:
        names |= formula_input.reachable.variables()
    return sorted(name for name in names if name in problem.types)


def parameter_variables(problem: CLoopProblem) -> list[str]:
    return [param.name for param in problem.parameters]


def value_terms_for_state(
    prefix: str,
    state: dict[str, Expr],
    types: dict[str, str],
    variables: list[str],
) -> list[ValueTerm]:
    return [
        (f"{prefix}_{name}", types[name], state.get(name, Var(name)))
        for name in variables
        if types[name] in {"Int", "Nat", "Bool"}
    ]


def value_terms_for_inputs(problem: CLoopProblem) -> list[ValueTerm]:
    return [(f"input_{param.name}", param.typ, Var(param.name)) for param in problem.parameters]


def init_counterexample_condition(problem: CLoopProblem, formula_input: FormulaInput, formula: Expr) -> Expr:
    variables = sorted_variables(problem.types)
    init_state = symbolic_execute(problem.init, {name: Var(name) for name in variables}, variables)
    return mk_and(
        [
            domain_expr(problem.types),
            formula_input.pre,
            mk_not(subst_map(formula, init_state)),
        ]
    )


def preservation_counterexample_condition(problem: CLoopProblem, formula: Expr) -> Expr:
    variables = sorted_variables(problem.types)
    before_state = {name: Var(name) for name in variables}
    after_state = symbolic_execute(problem.body, before_state, variables)
    return mk_and(
        [
            domain_expr(problem.types),
            formula,
            problem.guard,
            mk_not(subst_map(formula, after_state)),
        ]
    )


def find_reachable_counterexample_bounded(
    problem: CLoopProblem,
    formula_input: FormulaInput,
    formula: Expr,
    output_variables: list[str],
    unroll: int,
    z3_path: str,
    timeout: float,
) -> tuple[int, SolverResult] | None:
    variables = sorted_variables(problem.types)
    state = symbolic_execute(problem.init, {name: Var(name) for name in variables}, variables)
    path_conditions: list[Expr] = []

    for iteration in range(unroll + 1):
        condition = mk_and(
            [
                domain_expr(problem.types),
                formula_input.pre,
                *path_conditions,
                mk_not(subst_map(formula, state)),
            ]
        )
        result = check_sat_with_values(
            condition,
            problem.types,
            [
                *value_terms_for_inputs(problem),
                *value_terms_for_state("state", state, problem.types, output_variables),
            ],
            z3_path,
            timeout,
        )
        if result.status == "sat":
            return iteration, result
        if result.status != "unsat":
            return iteration, result
        path_conditions.append(subst_map(problem.guard, state))
        state = symbolic_execute(problem.body, state, variables)
    return None


def smt_and_text(parts: list[str]) -> str:
    actual = [part for part in parts if part and part != "true"]
    if not actual:
        return "true"
    if len(actual) == 1:
        return actual[0]
    return f"(and {' '.join(actual)})"


def self_increment(expr: Expr, name: str) -> int | None:
    if isinstance(expr, Var) and expr.name == name:
        return 0
    if isinstance(expr, Binary):
        if expr.op == "+":
            if isinstance(expr.left, Var) and expr.left.name == name and isinstance(expr.right, IntLit):
                return expr.right.value
            if isinstance(expr.right, Var) and expr.right.name == name and isinstance(expr.left, IntLit):
                return expr.left.value
        if expr.op == "-":
            if isinstance(expr.left, Var) and expr.left.name == name and isinstance(expr.right, IntLit):
                return -expr.right.value
    return None


def constant_increments(problem: CLoopProblem) -> dict[str, int] | None:
    variables = sorted_variables(problem.types)
    before_state = {name: Var(name) for name in variables}
    try:
        after_state = symbolic_execute(problem.body, before_state, variables)
    except InvariantError:
        return None
    increments: dict[str, int] = {}
    for name in variables:
        delta = self_increment(after_state.get(name, Var(name)), name)
        if delta is None:
            return None
        increments[name] = delta
    return increments


def add_iteration_delta(expr: Expr, delta: int, counter: Var) -> Expr:
    if delta == 0:
        return expr
    scaled = Binary("*", IntLit(abs(delta)), counter)
    if delta > 0:
        return Binary("+", expr, scaled)
    return Binary("-", expr, scaled)


@dataclasses.dataclass
class ReachabilityProof:
    status: str
    reason: str
    result: SolverResult | None = None


def find_reachable_counterexample_closed_form(
    problem: CLoopProblem,
    formula_input: FormulaInput,
    formula: Expr,
    output_variables: list[str],
    z3_path: str,
    timeout: float,
) -> ReachabilityProof:
    increments = constant_increments(problem)
    if increments is None:
        return ReachabilityProof("unsupported", "loop body is not a constant-increment transition")

    variables = sorted_variables(problem.types)
    init_state = symbolic_execute(problem.init, {name: Var(name) for name in variables}, variables)
    k = Var("__inv_k")
    j = Var("__inv_j")

    if "__inv_k" in problem.types or "__inv_j" in problem.types:
        return ReachabilityProof("unsupported", "variable names __inv_k and __inv_j are reserved")

    def state_at(counter: Var) -> dict[str, Expr]:
        return {
            name: add_iteration_delta(init_state.get(name, Var(name)), increments[name], counter)
            for name in variables
        }

    state_k = state_at(k)
    state_j = state_at(j)
    guard_j = subst_map(problem.guard, state_j).to_smt()
    prior_guards = (
        f"(forall (({smt_name(j.name)} Int)) "
        f"(=> (and (>= {smt_name(j.name)} 0) (< {smt_name(j.name)} {smt_name(k.name)})) "
        f"{guard_j}))"
    )
    condition_smt = smt_and_text(
        [
            domain_expr(problem.types).to_smt(),
            formula_input.pre.to_smt(),
            f"(>= {smt_name(k.name)} 0)",
            prior_guards,
            mk_not(subst_map(formula, state_k)).to_smt(),
        ]
    )
    result = check_sat_smt_with_values(
        condition_smt,
        problem.types,
        [
            ("iterations", "Int", k),
            *value_terms_for_inputs(problem),
            *value_terms_for_state("state", state_k, problem.types, output_variables),
        ],
        z3_path,
        timeout,
        extra_declarations=[f"(declare-const {smt_name(k.name)} Int)"],
    )
    if result.status == "unsat":
        return ReachabilityProof(
            "proved",
            "no k-step reachable loop-head state falsifies the candidate",
            result,
        )
    if result.status == "sat":
        return ReachabilityProof(
            "counterexample",
            "a reachable loop-head state falsifies the candidate",
            result,
        )
    return ReachabilityProof(result.status, f"closed-form reachability returned {result.status}", result)


def prove_with_reachable_fact(
    problem: CLoopProblem,
    formula_input: FormulaInput,
    formula: Expr,
    z3_path: str,
    timeout: float,
) -> tuple[bool, str]:
    if formula_input.reachable is None:
        return False, "no reachable fact supplied"
    fact_input = FormulaInput(formula_input.pre, [formula_input.reachable], None)
    fact_init = check_valid(initialized_vc(problem, fact_input, formula_input.reachable), problem.types, z3_path, timeout)
    if fact_init.status != "valid":
        return False, f"reachable fact is not initialized ({fact_init.status})"
    fact_pres = check_valid(preservation_vc(problem, formula_input.reachable), problem.types, z3_path, timeout)
    if fact_pres.status != "valid":
        return False, f"reachable fact is not preserved ({fact_pres.status})"
    implies_candidate = check_valid(
        implication(mk_and([domain_expr(problem.types), formula_input.reachable]), formula),
        problem.types,
        z3_path,
        timeout,
    )
    if implies_candidate.status != "valid":
        return False, f"reachable fact does not imply candidate ({implies_candidate.status})"
    return True, "supplied reachable fact is initialized, preserved, and implies the candidate"


@dataclasses.dataclass
class Classification:
    kind: str
    reason: str
    detail: dict[str, str] = dataclasses.field(default_factory=dict)
    inductive_counterexample: dict[str, str] = dataclasses.field(default_factory=dict)


def preservation_counterexample(
    problem: CLoopProblem,
    formula: Expr,
    output_variables: list[str],
    z3_path: str,
    timeout: float,
) -> dict[str, str]:
    variables = sorted_variables(problem.types)
    before_state = {name: Var(name) for name in variables}
    after_state = symbolic_execute(problem.body, before_state, variables)
    result = check_sat_with_values(
        preservation_counterexample_condition(problem, formula),
        problem.types,
        [
            *value_terms_for_state("before", before_state, problem.types, output_variables),
            *value_terms_for_state("after", after_state, problem.types, output_variables),
        ],
        z3_path,
        timeout,
    )
    return result.values


def classify_candidate(
    problem: CLoopProblem,
    formula_input: FormulaInput,
    formula: Expr,
    output_variables: list[str],
    unroll: int,
    z3_path: str,
    timeout: float,
) -> Classification:
    variables = sorted_variables(problem.types)
    init = check_valid(initialized_vc(problem, formula_input, formula), problem.types, z3_path, timeout)
    if init.status != "valid":
        init_state = symbolic_execute(problem.init, {name: Var(name) for name in variables}, variables)
        result = check_sat_with_values(
            init_counterexample_condition(problem, formula_input, formula),
            problem.types,
            [
                *value_terms_for_inputs(problem),
                *value_terms_for_state("state", init_state, problem.types, output_variables),
            ],
            z3_path,
            timeout,
        )
        return Classification(
            "Not an invariant",
            "candidate is false at an initial loop-head state",
            result.values,
        )

    pres = check_valid(preservation_vc(problem, formula), problem.types, z3_path, timeout)
    if pres.status == "valid":
        return Classification(
            "Inductive invariant",
            (
                "Z3 proved both obligations: initialization establishes the candidate, "
                "and candidate && guard is preserved by one loop-body step"
            ),
        )
    if pres.status not in {"invalid"}:
        return Classification(
            "Unknown",
            f"initialization is valid, but the preservation check returned {pres.status}",
            {"z3": pres.raw} if pres.raw else {},
        )

    noninductive_witness = preservation_counterexample(problem, formula, output_variables, z3_path, timeout)

    reachable_counterexample = find_reachable_counterexample_bounded(
        problem,
        formula_input,
        formula,
        output_variables,
        unroll,
        z3_path,
        timeout,
    )
    if reachable_counterexample is not None:
        iteration, result = reachable_counterexample
        if result.status == "sat":
            return Classification(
                "Not an invariant",
                f"candidate is false at a reachable loop-head state after {iteration} iteration(s)",
                {"iterations": str(iteration), **result.values},
                noninductive_witness,
            )
        return Classification(
            "Unknown",
            f"reachable-state search returned {result.status}",
            {"z3": result.raw} if result.raw else {},
            noninductive_witness,
        )

    closed = find_reachable_counterexample_closed_form(
        problem,
        formula_input,
        formula,
        output_variables,
        z3_path,
        timeout,
    )
    if closed.status == "proved":
        return Classification(
            "Non-inductive invariant",
            (
                "candidate holds at every reachable loop-head state; preservation still fails "
                "from arbitrary states satisfying only candidate && guard"
            ),
            {},
            noninductive_witness,
        )
    if closed.status == "counterexample" and closed.result is not None:
        return Classification(
            "Not an invariant",
            closed.reason,
            closed.result.values,
            noninductive_witness,
        )

    proved, proof_reason = prove_with_reachable_fact(problem, formula_input, formula, z3_path, timeout)
    if proved:
        return Classification(
            "Non-inductive invariant",
            f"{proof_reason}; one-step preservation fails",
            {},
            noninductive_witness,
        )

    return Classification(
        "Unknown",
        (
            f"candidate is initialized but not inductive; no reachable counterexample was found "
            f"up to {unroll} iteration(s), and invariance was not proved"
        ),
        {"reachability": closed.reason},
        noninductive_witness,
    )


def validate_formula_variables(problem: CLoopProblem, formula_input: FormulaInput) -> None:
    known = set(problem.types)
    formulas = [formula_input.pre, *formula_input.candidates]
    if formula_input.reachable is not None:
        formulas.append(formula_input.reachable)
    for formula in formulas:
        unknown = sorted(formula.variables() - known)
        if unknown:
            raise InvariantError(f"formula references unknown variable(s): {', '.join(unknown)}")


def print_values(values: dict[str, str]) -> None:
    if not values:
        return
    groups: dict[str, list[tuple[str, str]]] = {}
    for key, value in values.items():
        if "_" in key:
            prefix, name = key.split("_", 1)
        else:
            prefix, name = "value", key
        groups.setdefault(prefix, []).append((name, value))

    for prefix, pairs in groups.items():
        rendered = ", ".join(f"{name}={value}" for name, value in sorted(pairs))
        print(f"    {prefix}: {rendered}")


def print_problem_report(
    problem: CLoopProblem,
    formula_input: FormulaInput,
    classifications: list[tuple[Expr, Classification]],
) -> None:
    params = ", ".join(f"{param.name}:{param.typ}" for param in problem.parameters)
    print(f"\n== {problem.path} ==")
    print(f"function: {problem.function_name}({params})")
    print(f"loop guard: {problem.guard.to_source()}")
    if formula_input.pre != BoolLit(True):
        print(f"pre: {formula_input.pre.to_source()}")
    if formula_input.reachable is not None:
        print(f"reachable fact: {formula_input.reachable.to_source()}")
    for index, (formula, classification) in enumerate(classifications, start=1):
        print(f"[{classification.kind}] candidate {index}: {formula.to_source()}")
        print(f"    reason: {classification.reason}")
        print_values(classification.detail)
        if classification.inductive_counterexample:
            print("    Hoare triple counterexample for {candidate && guard} body {candidate}:")
            print_values(classification.inductive_counterexample)


def solve(input_c: Path, formula_file: Path, args: argparse.Namespace) -> bool:
    problem = parse_c_problem(input_c)
    formula_input = parse_formula_file(formula_file)
    validate_formula_variables(problem, formula_input)
    output_variables = displayed_variables(problem, formula_input)
    classifications = [
        (
            candidate,
            classify_candidate(
                problem,
                formula_input,
                candidate,
                output_variables,
                args.unroll,
                args.z3,
                args.timeout,
            ),
        )
        for candidate in formula_input.candidates
    ]
    print_problem_report(problem, formula_input, classifications)
    return all(classification.kind != "Unknown" for _, classification in classifications)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Classify a candidate invariant for the single top-level while loop in a C function."
    )
    parser.add_argument("input_c", type=Path, help="C file containing exactly one function")
    parser.add_argument("formula_file", type=Path, help="file containing a candidate invariant formula")
    parser.add_argument("--z3", default=shutil.which("z3") or "z3", help="path to z3 executable")
    parser.add_argument(
        "--unroll",
        type=int,
        default=20,
        help="bounded iterations used before the exact linear-loop reachability attempt",
    )
    parser.add_argument("--timeout", type=float, default=10.0, help="per-query Z3 timeout")
    args = parser.parse_args(argv)

    if not shutil.which(args.z3) and not Path(args.z3).exists():
        raise InvariantError(f"Z3 executable not found: {args.z3}")

    return 0 if solve(args.input_c, args.formula_file, args) else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except InvariantError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
