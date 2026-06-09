#!/usr/bin/env python3
"""Generate lecture-style Hoare annotations for a small C subset.

The parser intentionally accepts only the subset used in typical worksheet
programs: integer variables, assignments, if/else, while loops, and local
integer declarations.  C is parsed with pycparser; assertions are parsed as
mathematical integer formulas with support for chained comparisons such as
`l*l <= n < r*r`.
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

from pycparser import c_ast, c_parser


class AnnotatorError(Exception):
    pass


@dataclasses.dataclass(frozen=True)
class Expr:
    def subst(self, name: str, replacement: "Expr") -> "Expr":
        return self

    def variables(self) -> set[str]:
        return set()

    def to_smt(self) -> str:
        raise NotImplementedError


@dataclasses.dataclass(frozen=True)
class IntLit(Expr):
    value: int

    def to_smt(self) -> str:
        if self.value < 0:
            return f"(- {abs(self.value)})"
        return str(self.value)


@dataclasses.dataclass(frozen=True)
class BoolLit(Expr):
    value: bool

    def to_smt(self) -> str:
        return "true" if self.value else "false"


@dataclasses.dataclass(frozen=True)
class Var(Expr):
    name: str

    def subst(self, name: str, replacement: Expr) -> Expr:
        return replacement if self.name == name else self

    def variables(self) -> set[str]:
        return {self.name}

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

    def to_smt(self) -> str:
        if self.op == "-":
            return f"(- {self.expr.to_smt()})"
        if self.op == "!":
            return f"(not {self.expr.to_smt()})"
        raise AnnotatorError(f"unknown unary operator {self.op}")


@dataclasses.dataclass(frozen=True)
class Binary(Expr):
    op: str
    left: Expr
    right: Expr

    def subst(self, name: str, replacement: Expr) -> Expr:
        return Binary(self.op, self.left.subst(name, replacement), self.right.subst(name, replacement))

    def variables(self) -> set[str]:
        return self.left.variables() | self.right.variables()

    def to_smt(self) -> str:
        left = self.left.to_smt()
        right = self.right.to_smt()
        if self.op in {"+", "-", "*", "<", "<=", ">", ">="}:
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
        raise AnnotatorError(f"unknown binary operator {self.op}")


def smt_name(name: str) -> str:
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
        return name
    return "|" + name.replace("|", "||") + "|"


def mk_and(parts: Iterable[Expr]) -> Expr:
    items: list[Expr] = []
    for part in parts:
        if isinstance(part, BoolLit) and part.value:
            continue
        if isinstance(part, Binary) and part.op == "&&":
            items.extend(flatten_and(part))
        else:
            items.append(part)
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


def flatten_and(expr: Expr) -> list[Expr]:
    if isinstance(expr, Binary) and expr.op == "&&":
        return flatten_and(expr.left) + flatten_and(expr.right)
    return [expr]


PREC = {
    "=>": 1,
    "||": 2,
    "&&": 3,
    "==": 4,
    "!=": 4,
    "<": 5,
    "<=": 5,
    ">": 5,
    ">=": 5,
    "+": 6,
    "-": 6,
    "*": 7,
    "/": 7,
    "%": 7,
}


def pretty(expr: Expr, parent_prec: int = 0) -> str:
    if isinstance(expr, IntLit):
        return str(expr.value)
    if isinstance(expr, BoolLit):
        return "true" if expr.value else "false"
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Unary):
        inner = pretty(expr.expr, 8)
        if isinstance(expr.expr, Binary):
            inner = f"({pretty(expr.expr)})"
        return f"{expr.op}{inner}"
    if isinstance(expr, Binary):
        if expr.op == "&&":
            text = " && ".join(pretty(part, PREC["&&"]) for part in flatten_and(expr))
            return f"({text})" if PREC["&&"] < parent_prec else text
        prec = PREC[expr.op]
        left = pretty(expr.left, prec)
        right_parent = prec if expr.op == "=>" else prec + 1
        right = pretty(expr.right, right_parent)
        text = f"{left} {expr.op} {right}"
        return f"({text})" if prec < parent_prec else text
    raise AnnotatorError(f"cannot pretty-print expression {expr!r}")


@dataclasses.dataclass(frozen=True)
class Stmt:
    pass


@dataclasses.dataclass(frozen=True)
class Skip(Stmt):
    pass


@dataclasses.dataclass(frozen=True)
class Assign(Stmt):
    name: str
    expr: Expr


@dataclasses.dataclass(frozen=True)
class If(Stmt):
    cond: Expr
    then_body: list[Stmt]
    else_body: list[Stmt]


@dataclasses.dataclass(frozen=True)
class While(Stmt):
    cond: Expr
    body: list[Stmt]
    invariant: Expr | None = None


@dataclasses.dataclass
class Program:
    name: str
    params: list[str]
    body: list[Stmt]
    variables: set[str]


TOKEN_RE = re.compile(
    r"""
    (?P<space>[ \t\r\n]+)
  | (?P<int>\d+)
  | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<op>==|!=|<=|>=|&&|\|\||=>|[{}()+\-*/%<>=!])
    """,
    re.VERBOSE,
)


@dataclasses.dataclass(frozen=True)
class Token:
    kind: str
    value: str
    pos: int


def tokenize_assertion(text: str) -> list[Token]:
    tokens: list[Token] = []
    pos = 0
    for match in TOKEN_RE.finditer(text):
        if match.start() != pos:
            raise AnnotatorError(f"unexpected assertion text near {text[pos:match.start()]!r}")
        pos = match.end()
        if match.lastgroup == "space":
            continue
        value = match.group(0)
        if match.lastgroup == "id" and value in {"true", "false", "and", "or", "not"}:
            tokens.append(Token(value, value, match.start()))
        elif match.lastgroup == "id":
            tokens.append(Token("id", value, match.start()))
        elif match.lastgroup == "int":
            tokens.append(Token("int", value, match.start()))
        else:
            tokens.append(Token(value, value, match.start()))
    if pos != len(text):
        raise AnnotatorError(f"unexpected assertion text near {text[pos:]!r}")
    tokens.append(Token("eof", "", len(text)))
    return tokens


class AssertionParser:
    def __init__(self, text: str):
        stripped = strip_outer_braces(text.strip())
        self.tokens = tokenize_assertion(stripped)
        self.i = 0

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
        if token is None:
            cur = self.current()
            raise AnnotatorError(f"expected {kind!r} in assertion, got {cur.kind!r}")
        return token

    def parse(self) -> Expr:
        expr = self.parse_implies()
        self.expect("eof")
        return expr

    def parse_implies(self) -> Expr:
        left = self.parse_or()
        if self.match("=>"):
            return Binary("=>", left, self.parse_implies())
        return left

    def parse_or(self) -> Expr:
        expr = self.parse_and()
        while self.match("||") or self.match("or"):
            expr = Binary("||", expr, self.parse_and())
        return expr

    def parse_and(self) -> Expr:
        expr = self.parse_comparison()
        while self.match("&&") or self.match("and"):
            expr = Binary("&&", expr, self.parse_comparison())
        return expr

    def parse_comparison(self) -> Expr:
        left = self.parse_add()
        relations: list[tuple[str, Expr, Expr]] = []
        while self.current().kind in {"==", "!=", "=", "<", "<=", ">", ">="}:
            op = self.current().kind
            self.i += 1
            if op == "=":
                op = "=="
            right = self.parse_add()
            relations.append((op, left, right))
            left = right
        if not relations:
            return left
        return mk_and(Binary(op, lhs, rhs) for op, lhs, rhs in relations)

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
        if self.match("+"):
            return self.parse_unary()
        return self.parse_primary()

    def parse_primary(self) -> Expr:
        if token := self.match("int"):
            return IntLit(int(token.value))
        if token := self.match("id"):
            return Var(token.value)
        if self.match("true"):
            return BoolLit(True)
        if self.match("false"):
            return BoolLit(False)
        if self.match("("):
            expr = self.parse_implies()
            self.expect(")")
            return expr
        cur = self.current()
        raise AnnotatorError(f"expected expression in assertion, got {cur.kind!r}")


def strip_outer_braces(text: str) -> str:
    if text.startswith("{") and text.endswith("}"):
        return text[1:-1].strip()
    return text


def parse_assertion(text: str) -> Expr:
    return AssertionParser(text).parse()


def strip_c_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return re.sub(r"//[^\n]*", "", text)


def parse_c_program(path: Path) -> Program:
    text = strip_c_comments(path.read_text(encoding="utf-8"))
    try:
        ast = c_parser.CParser().parse(text, filename=str(path))
    except Exception as exc:  # pycparser raises ParseError without a shared base
        raise AnnotatorError(f"could not parse C input: {exc}") from exc

    funcs = [node for _, node in ast.children() if isinstance(node, c_ast.FuncDef)]
    if len(funcs) != 1:
        raise AnnotatorError(f"expected exactly one C function, found {len(funcs)}")
    func = funcs[0]
    variables = set(extract_params(func))
    body = convert_compound(func.body, variables)
    return Program(func.decl.name, sorted(extract_params(func)), body, variables)


def extract_params(func: c_ast.FuncDef) -> list[str]:
    typ = func.decl.type
    if not isinstance(typ, c_ast.FuncDecl) or typ.args is None:
        return []
    params = []
    for param in typ.args.params:
        if isinstance(param, c_ast.EllipsisParam):
            raise AnnotatorError("variadic functions are not supported")
        if not isinstance(param, c_ast.Decl) or param.name is None:
            continue
        ensure_int_decl(param, f"parameter {param.name}")
        params.append(param.name)
    return params


def ensure_int_decl(decl: c_ast.Decl, label: str) -> None:
    typ = decl.type
    if isinstance(typ, c_ast.TypeDecl):
        inner = typ.type
        if isinstance(inner, c_ast.IdentifierType) and inner.names == ["int"]:
            return
    raise AnnotatorError(f"{label} must be an int")


def convert_compound(node: c_ast.Compound, variables: set[str]) -> list[Stmt]:
    stmts: list[Stmt] = []
    for item in node.block_items or []:
        stmts.extend(convert_item(item, variables))
    return stmts


def convert_item(node: c_ast.Node, variables: set[str]) -> list[Stmt]:
    if isinstance(node, c_ast.Decl):
        ensure_int_decl(node, f"local variable {node.name}")
        if node.name is not None:
            variables.add(node.name)
        if node.init is None:
            return []
        return [Assign(node.name, convert_expr(node.init))]
    if isinstance(node, c_ast.Assignment):
        if node.op != "=":
            raise AnnotatorError(f"unsupported assignment operator {node.op!r}")
        if not isinstance(node.lvalue, c_ast.ID):
            raise AnnotatorError("only simple variable assignments are supported")
        variables.add(node.lvalue.name)
        return [Assign(node.lvalue.name, convert_expr(node.rvalue))]
    if isinstance(node, c_ast.While):
        if not isinstance(node.stmt, c_ast.Compound):
            raise AnnotatorError("while bodies must use braces")
        return [While(convert_expr(node.cond), convert_compound(node.stmt, variables))]
    if isinstance(node, c_ast.If):
        then_body = convert_branch(node.iftrue, variables)
        else_body = convert_branch(node.iffalse, variables) if node.iffalse is not None else []
        return [If(convert_expr(node.cond), then_body, else_body)]
    if isinstance(node, c_ast.Compound):
        return convert_compound(node, variables)
    if isinstance(node, c_ast.EmptyStatement):
        return [Skip()]
    raise AnnotatorError(f"unsupported C statement: {node.__class__.__name__}")


def convert_branch(node: c_ast.Node | None, variables: set[str]) -> list[Stmt]:
    if node is None:
        return []
    if isinstance(node, c_ast.Compound):
        return convert_compound(node, variables)
    return convert_item(node, variables)


def convert_expr(node: c_ast.Node) -> Expr:
    if isinstance(node, c_ast.ID):
        return Var(node.name)
    if isinstance(node, c_ast.Constant):
        if node.type != "int":
            raise AnnotatorError(f"only integer constants are supported, got {node.type}")
        return IntLit(int(node.value, 0))
    if isinstance(node, c_ast.BinaryOp):
        if node.op not in {"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "||"}:
            raise AnnotatorError(f"unsupported binary operator {node.op!r}")
        return Binary(node.op, convert_expr(node.left), convert_expr(node.right))
    if isinstance(node, c_ast.UnaryOp):
        if node.op == "+":
            return convert_expr(node.expr)
        if node.op in {"-", "!"}:
            return Unary(node.op, convert_expr(node.expr))
        raise AnnotatorError(f"unsupported unary operator {node.op!r}")
    if isinstance(node, c_ast.Cast):
        return convert_expr(node.expr)
    raise AnnotatorError(f"unsupported C expression: {node.__class__.__name__}")


def with_invariant(stmts: list[Stmt], invariant: Expr) -> list[Stmt]:
    return [attach_invariant(stmt, invariant) for stmt in stmts]


def attach_invariant(stmt: Stmt, invariant: Expr) -> Stmt:
    if isinstance(stmt, While):
        return While(stmt.cond, with_invariant(stmt.body, invariant), invariant)
    if isinstance(stmt, If):
        return If(stmt.cond, with_invariant(stmt.then_body, invariant), with_invariant(stmt.else_body, invariant))
    return stmt


def count_loops(stmts: list[Stmt]) -> int:
    total = 0
    for stmt in stmts:
        if isinstance(stmt, While):
            total += 1 + count_loops(stmt.body)
        elif isinstance(stmt, If):
            total += count_loops(stmt.then_body) + count_loops(stmt.else_body)
    return total


def wp_block(stmts: list[Stmt], post: Expr, checker: "Checker | None" = None) -> Expr:
    current = post
    for stmt in reversed(stmts):
        current = wp_stmt(stmt, current, checker)
    return current


def wp_stmt(stmt: Stmt, post: Expr, checker: "Checker | None" = None) -> Expr:
    if isinstance(stmt, Skip):
        return post
    if isinstance(stmt, Assign):
        return post.subst(stmt.name, stmt.expr)
    if isinstance(stmt, If):
        then_wp = wp_block(stmt.then_body, post, checker)
        else_wp = wp_block(stmt.else_body, post, checker)
        return mk_and([mk_implies(stmt.cond, then_wp), mk_implies(mk_not(stmt.cond), else_wp)])
    if isinstance(stmt, While):
        if stmt.invariant is None:
            raise AnnotatorError("while loop has no invariant")
        return stmt.invariant
    raise AnnotatorError(f"unknown statement {stmt!r}")


def annotation_pre(stmt: Stmt, post: Expr, checker: "Checker | None") -> Expr:
    if isinstance(stmt, If):
        readable = readable_if_pre(stmt, post, checker)
        if readable is not None:
            return readable
    return wp_stmt(stmt, post, checker)


def readable_if_pre(stmt: If, post: Expr, checker: "Checker | None") -> Expr | None:
    then_wp = wp_block(stmt.then_body, post, checker)
    else_wp = wp_block(stmt.else_body, post, checker)
    if checker is None:
        return None
    then_ok = checker.proves(mk_and([post, stmt.cond]), then_wp)
    else_ok = checker.proves(mk_and([post, mk_not(stmt.cond)]), else_wp)
    if then_ok and else_ok:
        return post
    return None


def annotation_pairs(stmts: list[Stmt], post: Expr, checker: "Checker | None") -> list[tuple[Stmt, Expr, Expr]]:
    current = post
    result: list[tuple[Stmt, Expr, Expr]] = []
    for stmt in reversed(stmts):
        pre = annotation_pre(stmt, current, checker)
        result.append((stmt, pre, current))
        current = pre
    return list(reversed(result))


class Checker:
    def __init__(self, variables: Iterable[str], z3_path: str, timeout: float):
        self.variables = sorted(set(variables))
        self.z3_path = z3_path
        self.timeout = timeout
        self.enabled = bool(shutil.which(z3_path) or Path(z3_path).exists())

    def proves(self, antecedent: Expr, consequent: Expr) -> bool:
        if not self.enabled:
            return False
        expr = mk_implies(antecedent, consequent)
        declarations = "\n".join(f"(declare-const {smt_name(name)} Int)" for name in self.variables)
        script = "\n".join(
            part
            for part in [
                declarations,
                f"(assert (not {expr.to_smt()}))",
                "(check-sat)",
            ]
            if part
        ) + "\n"
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
            fh.write(script)
            smt_path = fh.name
        try:
            result = subprocess.run(
                [self.z3_path, "-smt2", smt_path],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                timeout=self.timeout,
                check=False,
            )
        except subprocess.TimeoutExpired:
            return False
        finally:
            Path(smt_path).unlink(missing_ok=True)
        return result.stdout.strip().splitlines()[:1] == ["unsat"]


class Renderer:
    def __init__(self, checker: Checker | None):
        self.checker = checker

    def render(self, program: Program, pre: Expr | None, post: Expr | None) -> str:
        loop_count = count_loops(program.body)
        if loop_count != 1:
            raise AnnotatorError(f"expected exactly one while loop, found {loop_count}")
        body = program.body
        first_loop = find_first_loop(body)
        assert first_loop.invariant is not None

        final_post = post
        if final_post is None:
            inferred = infer_exit_post(first_loop.invariant, first_loop.cond)
            final_post = inferred.final if inferred else mk_and([first_loop.invariant, mk_not(first_loop.cond)])

        initial_needed = wp_block(body, final_post, self.checker)
        initial = pre or initial_needed

        lines: list[str] = []
        append_assertion(lines, 0, initial, None)
        if initial != initial_needed:
            self.append_consequence(lines, 0, initial, initial_needed)
        self.render_block(lines, body, initial_needed, final_post, 0)
        return "\n".join(lines).rstrip() + "\n"

    def render_block(
        self,
        lines: list[str],
        stmts: list[Stmt],
        incoming: Expr,
        outgoing: Expr,
        indent: int,
    ) -> None:
        current = incoming
        for stmt, pre, post in annotation_pairs(stmts, outgoing, self.checker):
            if pre != current:
                self.append_consequence(lines, indent, current, pre)
            self.render_stmt(lines, stmt, pre, post, indent)
            current = post

    def render_stmt(self, lines: list[str], stmt: Stmt, pre: Expr, post: Expr, indent: int) -> None:
        pad = " " * indent
        if isinstance(stmt, Assign):
            lines.append(f"{pad}{stmt.name} = {pretty(stmt.expr)};")
            lines.append("")
            append_assertion(lines, indent, post, "assignment rule")
            return

        if isinstance(stmt, Skip):
            lines.append(f"{pad}skip;")
            lines.append("")
            append_assertion(lines, indent, post, "skip rule")
            return

        if isinstance(stmt, If):
            lines.append(f"{pad}if ({pretty(stmt.cond)}) {{")
            then_incoming = mk_and([pre, stmt.cond])
            append_assertion(lines, indent + 4, then_incoming, "conditional rule")
            self.render_block(lines, stmt.then_body, then_incoming, post, indent + 4)
            if stmt.else_body:
                lines.append(f"{pad}}} else {{")
                else_incoming = mk_and([pre, mk_not(stmt.cond)])
                append_assertion(lines, indent + 4, else_incoming, "conditional rule")
                self.render_block(lines, stmt.else_body, else_incoming, post, indent + 4)
            lines.append(f"{pad}}}")
            lines.append("")
            append_assertion(lines, indent, post, "conditional rule")
            return

        if isinstance(stmt, While):
            if stmt.invariant is None:
                raise AnnotatorError("while loop has no invariant")
            append_assertion(lines, indent, stmt.invariant, "invariant")
            lines.append(f"{pad}while ({pretty(stmt.cond)}) {{")
            body_incoming = mk_and([stmt.invariant, stmt.cond])
            append_assertion(lines, indent + 4, body_incoming, "while rule")
            self.render_block(lines, stmt.body, body_incoming, stmt.invariant, indent + 4)
            lines.append(f"{pad}}}")
            lines.append("")
            self.render_loop_exit(lines, indent, stmt, post)
            return

        raise AnnotatorError(f"unknown statement {stmt!r}")

    def render_loop_exit(self, lines: list[str], indent: int, stmt: While, post: Expr) -> None:
        assert stmt.invariant is not None
        loop_exit = mk_and([stmt.invariant, mk_not(stmt.cond)])
        append_assertion(lines, indent, loop_exit, "while rule")
        if post == loop_exit:
            return
        inferred = infer_exit_post(stmt.invariant, stmt.cond)
        if inferred and inferred.final == post:
            for step in inferred.steps:
                append_assertion(lines, indent, step, "consequence rule")
            return
        self.append_consequence(lines, indent, loop_exit, post)

    def append_consequence(self, lines: list[str], indent: int, current: Expr, target: Expr) -> None:
        for step in consequence_steps(current, target):
            append_assertion(lines, indent, step, "consequence rule")


def append_assertion(lines: list[str], indent: int, expr: Expr, rule: str | None) -> None:
    pad = " " * indent
    lines.append(f"{pad}{{ {pretty(expr)} }}")
    if rule:
        lines.append(f"{pad}// {rule}")
    lines.append("")


def consequence_steps(current: Expr, target: Expr) -> list[Expr]:
    normalized = normalize_negated_comparisons(current)
    if normalized != current and normalized != target:
        return [normalized, target]
    return [target]


def normalize_negated_comparisons(expr: Expr) -> Expr:
    if isinstance(expr, Binary):
        return Binary(expr.op, normalize_negated_comparisons(expr.left), normalize_negated_comparisons(expr.right))
    if isinstance(expr, Unary) and expr.op == "!" and isinstance(expr.expr, Binary):
        op = {
            "<=": ">",
            "<": ">=",
            ">=": "<",
            ">": "<=",
            "==": "!=",
            "!=": "==",
        }.get(expr.expr.op)
        if op:
            return Binary(op, expr.expr.left, expr.expr.right)
    if isinstance(expr, Unary):
        return Unary(expr.op, normalize_negated_comparisons(expr.expr))
    return expr


@dataclasses.dataclass(frozen=True)
class ExitInference:
    final: Expr
    steps: list[Expr]


def infer_exit_post(invariant: Expr, cond: Expr) -> ExitInference | None:
    if not (isinstance(cond, Binary) and cond.op == "!="):
        return None
    equality = Binary("==", cond.left, cond.right)
    first = mk_and([invariant, equality])
    solved = solve_equality_for_substitution(equality)
    if solved is None:
        return ExitInference(first, [first])
    name, replacement, solved_equality = solved
    second = mk_and([invariant, solved_equality])
    final = invariant.subst(name, replacement)
    return ExitInference(final, [first, second, final])


def solve_equality_for_substitution(equality: Binary) -> tuple[str, Expr, Expr] | None:
    assert equality.op == "=="
    result = solve_side(equality.left, equality.right)
    if result is not None:
        return result
    return solve_side(equality.right, equality.left)


def solve_side(left: Expr, right: Expr) -> tuple[str, Expr, Expr] | None:
    if not isinstance(left, Var) or not isinstance(right, Binary):
        return None
    if right.op == "-" and isinstance(right.left, Var) and isinstance(right.right, IntLit):
        replacement = Binary("+", left, right.right)
        solved = Binary("==", right.left, replacement)
        return right.left.name, replacement, solved
    if right.op == "+" and isinstance(right.left, Var) and isinstance(right.right, IntLit):
        replacement = Binary("-", left, right.right)
        solved = Binary("==", right.left, replacement)
        return right.left.name, replacement, solved
    return None


def find_first_loop(stmts: list[Stmt]) -> While:
    for stmt in stmts:
        if isinstance(stmt, While):
            return stmt
        if isinstance(stmt, If):
            try:
                return find_first_loop(stmt.then_body)
            except AnnotatorError:
                return find_first_loop(stmt.else_body)
    raise AnnotatorError("the input program has no while loop")


def read_inline_or_file(value: str) -> str:
    path = Path(value)
    if path.exists() and path.is_file():
        return path.read_text(encoding="utf-8").strip()
    return value


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate Hoare-logic annotations for a small integer C function."
    )
    parser.add_argument("c_file", type=Path, help="C file containing exactly one function")
    parser.add_argument("invariant", help="loop invariant, either inline or as a file path")
    parser.add_argument("--pre", help="optional precondition assertion")
    parser.add_argument("--post", help="optional final postcondition assertion")
    parser.add_argument("--output", "-o", type=Path, help="write annotated program to this file")
    parser.add_argument("--z3", default=shutil.which("z3") or "z3", help="path to z3 executable")
    parser.add_argument("--timeout", type=float, default=3.0, help="per-query Z3 timeout")
    parser.add_argument(
        "--no-z3",
        action="store_true",
        help="do not use Z3 to choose shorter consequence annotations",
    )
    return parser


def main(argv: list[str]) -> int:
    args = build_arg_parser().parse_args(argv)
    program = parse_c_program(args.c_file)
    invariant = parse_assertion(read_inline_or_file(args.invariant))
    pre = parse_assertion(read_inline_or_file(args.pre)) if args.pre else None
    post = parse_assertion(read_inline_or_file(args.post)) if args.post else None

    referenced = set(invariant.variables())
    if pre is not None:
        referenced |= pre.variables()
    if post is not None:
        referenced |= post.variables()
    unknown = sorted(referenced - program.variables)
    if unknown:
        raise AnnotatorError("assertion mentions unknown variable(s): " + ", ".join(unknown))

    body = with_invariant(program.body, invariant)
    program = dataclasses.replace(program, body=body)

    checker = None if args.no_z3 else Checker(program.variables, args.z3, args.timeout)
    output = Renderer(checker).render(program, pre, post)

    if args.output:
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except AnnotatorError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
