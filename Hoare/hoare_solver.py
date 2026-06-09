#!/usr/bin/env python3
"""Small Hoare-logic verification-condition generator.

The supported language is intentionally close to the textbook while-language:
assignments, skip, if/else, while loops with explicit invariants, and optional
assertion cut-points.  The tool computes weakest preconditions, emits proof
obligations tagged with the Hoare rule that produced them, and asks the Z3
command-line solver to prove each obligation.
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


class HoareError(Exception):
    pass


@dataclasses.dataclass(frozen=True)
class Token:
    kind: str
    value: str
    line: int
    col: int


KEYWORDS = {
    "and",
    "assert",
    "bool",
    "candidate",
    "do",
    "else",
    "false",
    "fi",
    "init",
    "if",
    "invariant",
    "int",
    "nat",
    "not",
    "od",
    "or",
    "post",
    "pre",
    "reachable",
    "skip",
    "then",
    "true",
    "vars",
    "while",
}


TOKEN_RE = re.compile(
    r"""
    (?P<space>[ \t\r\n]+)
  | (?P<line_comment>//[^\n]*|\#[^\n]*)
  | (?P<block_comment>/\*.*?\*/)
  | (?P<int>\d+)
  | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<op>:=|==|!=|<=|>=|&&|\|\||=>|[{}();,+\-*/%<>=!])
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
            raise HoareError(f"unexpected text at {line}:{col}: {snippet!r}")

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
        raise HoareError(f"unexpected text at {line}:{col}: {snippet!r}")
    tokens.append(Token("eof", "", line, col))
    return tokens


@dataclasses.dataclass(frozen=True)
class Expr:
    def subst(self, name: str, replacement: Expr) -> Expr:
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
        raise HoareError(f"unknown unary operator {self.op}")


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
        raise HoareError(f"unknown binary operator {self.op}")


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
class Assert(Stmt):
    expr: Expr

    def variables(self) -> set[str]:
        return self.expr.variables()


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


@dataclasses.dataclass(frozen=True)
class While(Stmt):
    cond: Expr
    invariant: Expr | None
    body: list[Stmt]

    def variables(self) -> set[str]:
        names = self.cond.variables()
        if self.invariant is not None:
            names |= self.invariant.variables()
        for stmt in self.body:
            names |= stmt.variables()
        return names


@dataclasses.dataclass
class Program:
    declarations: dict[str, str]
    pre: Expr
    body: list[Stmt]
    post: Expr
    path: Path
    title: str | None = None

    def variables(self) -> set[str]:
        names = self.pre.variables() | self.post.variables() | set(self.declarations)
        for stmt in self.body:
            names |= stmt.variables()
        return names


class Parser:
    def __init__(self, tokens: list[Token], path: Path):
        self.tokens = tokens
        self.i = 0
        self.path = path
        self.declarations: dict[str, str] = {}

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
            raise HoareError(
                f"{self.path}:{cur.line}:{cur.col}: expected {kind!r}, got {cur.kind!r}"
            )
        return token

    def parse(self) -> Program:
        while self.at("vars"):
            self.parse_declaration()
        if self.match("pre"):
            pre = self.parse_braced_expr()
            body: list[Stmt] = []
            while not self.at("post") and not self.at("eof"):
                body.append(self.parse_stmt())
            self.expect("post")
            post = self.parse_braced_expr()
            self.expect("eof")
            return Program(self.declarations, pre, body, post, self.path)

        pre = self.parse_braced_expr()
        body = []
        post: Expr | None = None
        while not self.at("eof"):
            if self.is_final_braced_expr():
                post = self.parse_braced_expr()
                self.match(";")
                break
            body.append(self.parse_stmt())
        self.expect("eof")
        if post is None:
            raise HoareError(f"{self.path}: lecture-style programs must end with a final {{post}} assertion")
        return Program(self.declarations, pre, body, post, self.path)

    def is_final_braced_expr(self) -> bool:
        if not self.at("{"):
            return False
        depth = 0
        j = self.i
        while j < len(self.tokens):
            if self.tokens[j].kind == "{":
                depth += 1
            elif self.tokens[j].kind == "}":
                depth -= 1
                if depth == 0:
                    j += 1
                    if self.tokens[j].kind == ";":
                        j += 1
                    return self.tokens[j].kind == "eof"
            j += 1
        return False

    def parse_declaration(self) -> None:
        self.expect("vars")
        if self.match("int"):
            typ = "Int"
        elif self.match("bool"):
            typ = "Bool"
        else:
            cur = self.current()
            raise HoareError(f"{self.path}:{cur.line}:{cur.col}: expected int or bool")

        while True:
            name = self.expect("id").value
            old = self.declarations.get(name)
            if old and old != typ:
                raise HoareError(f"{self.path}: conflicting declarations for {name}")
            self.declarations[name] = typ
            if not self.match(","):
                break
        self.expect(";")

    def parse_stmt(self) -> Stmt:
        if self.at("{"):
            line = self.current().line
            expr = self.parse_braced_expr()
            self.match(";")
            return Assert(line, expr)

        if token := self.match("skip"):
            self.match(";")
            return Skip(token.line)

        if token := self.match("assert"):
            expr = self.parse_braced_expr()
            self.match(";")
            return Assert(token.line, expr)

        if token := self.match("if"):
            if self.match("("):
                cond = self.parse_expr()
                self.expect(")")
                then_body = self.parse_block()
                else_body = self.parse_block() if self.match("else") else []
            else:
                cond = self.parse_expr()
                self.expect("then")
                then_body = self.parse_until({"else", "fi"})
                else_body = []
                if self.match("else"):
                    else_body = self.parse_until({"fi"})
                self.expect("fi")
            return If(token.line, cond, then_body, else_body)

        if token := self.match("while"):
            if self.match("("):
                cond = self.parse_expr()
                self.expect(")")
                invariant = self.parse_optional_invariant()
                if self.at("{"):
                    invariant, body = self.parse_while_block(invariant)
                else:
                    self.expect("do")
                    body = self.parse_until({"od"})
                    self.expect("od")
            else:
                cond = self.parse_expr()
                invariant = self.parse_optional_invariant()
                self.expect("do")
                body = self.parse_until({"od"})
                self.expect("od")
            return While(token.line, cond, invariant, body)

        name_token = self.expect("id")
        if not (self.match(":=") or self.match("=")):
            cur = self.current()
            raise HoareError(f"{self.path}:{cur.line}:{cur.col}: expected assignment operator")
        expr = self.parse_expr()
        self.match(";")
        return Assign(name_token.line, name_token.value, expr)

    def parse_optional_invariant(self) -> Expr | None:
        if self.match("invariant"):
            return self.parse_braced_expr()
        return None

    def parse_while_block(self, invariant: Expr | None) -> tuple[Expr | None, list[Stmt]]:
        self.expect("{")
        if self.at("invariant"):
            if invariant is not None:
                cur = self.current()
                raise HoareError(f"{self.path}:{cur.line}:{cur.col}: duplicate loop invariant")
            invariant = self.parse_optional_invariant()

        body: list[Stmt] = []
        while not self.at("}"):
            if self.at("eof"):
                cur = self.current()
                raise HoareError(f"{self.path}:{cur.line}:{cur.col}: unterminated block")
            body.append(self.parse_stmt())
        self.expect("}")
        return invariant, body

    def parse_block(self) -> list[Stmt]:
        self.expect("{")
        body: list[Stmt] = []
        while not self.at("}"):
            if self.at("eof"):
                cur = self.current()
                raise HoareError(f"{self.path}:{cur.line}:{cur.col}: unterminated block")
            body.append(self.parse_stmt())
        self.expect("}")
        return body

    def parse_until(self, terminators: set[str]) -> list[Stmt]:
        body: list[Stmt] = []
        while not self.at("eof") and self.current().kind not in terminators:
            body.append(self.parse_stmt())
        if self.at("eof"):
            cur = self.current()
            expected = " or ".join(sorted(terminators))
            raise HoareError(f"{self.path}:{cur.line}:{cur.col}: expected {expected}")
        return body

    def parse_braced_expr(self) -> Expr:
        self.expect("{")
        expr = self.parse_expr()
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
        raise HoareError(f"{self.path}:{cur.line}:{cur.col}: expected expression")


@dataclasses.dataclass
class VC:
    name: str
    expr: Expr
    rule: str
    premise: str
    line: int


def wp_block(stmts: list[Stmt], post: Expr, vcs: list[VC]) -> Expr:
    current = post
    for stmt in reversed(stmts):
        current = wp_stmt(stmt, current, vcs)
    return current


def wp_stmt(stmt: Stmt, post: Expr, vcs: list[VC]) -> Expr:
    if isinstance(stmt, Skip):
        return post

    if isinstance(stmt, Assign):
        return post.subst(stmt.name, stmt.expr)

    if isinstance(stmt, Assert):
        vcs.append(
            VC(
                name=f"assertion at line {stmt.line} is strong enough for following code",
                expr=mk_implies(stmt.expr, post),
                rule="Consequence / annotation cut",
                premise=f"asserted condition implies next weakest precondition: {post.to_source()}",
                line=stmt.line,
            )
        )
        return stmt.expr

    if isinstance(stmt, If):
        then_wp = wp_block(stmt.then_body, post, vcs)
        else_wp = wp_block(stmt.else_body, post, vcs)
        return mk_and(
            [
                mk_implies(stmt.cond, then_wp),
                mk_implies(mk_not(stmt.cond), else_wp),
            ]
        )

    if isinstance(stmt, While):
        if stmt.invariant is None:
            raise HoareError(f"loop at line {stmt.line} has no invariant")
        body_wp = wp_block(stmt.body, stmt.invariant, vcs)
        vcs.append(
            VC(
                name=f"loop invariant preserved at line {stmt.line}",
                expr=mk_implies(mk_and([stmt.invariant, stmt.cond]), body_wp),
                rule="While",
                premise="{I && B} body {I}",
                line=stmt.line,
            )
        )
        vcs.append(
            VC(
                name=f"loop exit establishes following postcondition at line {stmt.line}",
                expr=mk_implies(mk_and([stmt.invariant, mk_not(stmt.cond)]), post),
                rule="While + Consequence",
                premise="I && !B implies the postcondition after the loop",
                line=stmt.line,
            )
        )
        return stmt.invariant

    raise HoareError(f"unknown statement: {stmt!r}")


def infer_types(program: Program) -> dict[str, str]:
    env = dict(program.declarations)

    def set_type(name: str, typ: str) -> None:
        old = env.get(name)
        if old and old != typ:
            raise HoareError(f"{program.path}: inferred conflicting types for {name}: {old} and {typ}")
        env[name] = typ

    def infer_expr(expr: Expr, expected: str | None = None) -> str | None:
        if isinstance(expr, IntLit):
            return "Int"
        if isinstance(expr, BoolLit):
            return "Bool"
        if isinstance(expr, Var):
            if expected:
                set_type(expr.name, expected)
                return expected
            return env.get(expr.name)
        if isinstance(expr, Unary):
            if expr.op == "-":
                infer_expr(expr.expr, "Int")
                return "Int"
            if expr.op == "!":
                infer_expr(expr.expr, "Bool")
                return "Bool"
        if isinstance(expr, Binary):
            if expr.op in {"+", "-", "*", "/", "%", "<", "<=", ">", ">="}:
                infer_expr(expr.left, "Int")
                infer_expr(expr.right, "Int")
                return "Bool" if expr.op in {"<", "<=", ">", ">="} else "Int"
            if expr.op in {"&&", "||", "=>"}:
                infer_expr(expr.left, "Bool")
                infer_expr(expr.right, "Bool")
                return "Bool"
            if expr.op in {"==", "!="}:
                left_type = infer_expr(expr.left)
                right_type = infer_expr(expr.right)
                if left_type and right_type and left_type != right_type:
                    raise HoareError(
                        f"{program.path}: equality compares {left_type} with {right_type}: {expr.to_source()}"
                    )
                if left_type:
                    infer_expr(expr.right, left_type)
                if right_type:
                    infer_expr(expr.left, right_type)
                return "Bool"
        return None

    def walk_stmt(stmt: Stmt) -> None:
        if isinstance(stmt, Assign):
            typ = infer_expr(stmt.expr)
            if typ:
                set_type(stmt.name, typ)
        elif isinstance(stmt, Assert):
            infer_expr(stmt.expr, "Bool")
        elif isinstance(stmt, If):
            infer_expr(stmt.cond, "Bool")
            for inner in stmt.then_body + stmt.else_body:
                walk_stmt(inner)
        elif isinstance(stmt, While):
            infer_expr(stmt.cond, "Bool")
            if stmt.invariant is not None:
                infer_expr(stmt.invariant, "Bool")
            for inner in stmt.body:
                walk_stmt(inner)

    infer_expr(program.pre, "Bool")
    infer_expr(program.post, "Bool")
    for stmt in program.body:
        walk_stmt(stmt)
    for name in program.variables():
        env.setdefault(name, "Int")
    return env


@dataclasses.dataclass
class CheckResult:
    status: str
    model: str = ""
    raw: str = ""


def smt_script(expr: Expr, types: dict[str, str], with_model: bool = False) -> str:
    declarations = "\n".join(
        f"(declare-const {smt_name(name)} {typ})" for name, typ in sorted(types.items())
    )
    commands = [
        "(set-option :produce-models true)",
        declarations,
        f"(assert (not {expr.to_smt()}))",
        "(check-sat)",
    ]
    if with_model:
        commands.append("(get-model)")
    return "\n".join(part for part in commands if part) + "\n"


def run_z3(expr: Expr, types: dict[str, str], z3_path: str, timeout: float) -> CheckResult:
    def invoke(with_model: bool) -> subprocess.CompletedProcess[str]:
        script = smt_script(expr, types, with_model=with_model)
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as fh:
            fh.write(script)
            smt_path = fh.name
        try:
            return subprocess.run(
                [z3_path, "-smt2", smt_path],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout,
                check=False,
            )
        finally:
            Path(smt_path).unlink(missing_ok=True)

    try:
        result = invoke(with_model=False)
    except subprocess.TimeoutExpired:
        return CheckResult("timeout")
    raw = (result.stdout + result.stderr).strip()
    first_line = result.stdout.strip().splitlines()[0] if result.stdout.strip() else ""
    if first_line == "unsat":
        return CheckResult("valid", raw=raw)
    if first_line == "sat":
        try:
            model_result = invoke(with_model=True)
            model = "\n".join(model_result.stdout.strip().splitlines()[1:])
        except subprocess.TimeoutExpired:
            model = ""
        return CheckResult("invalid", model=model, raw=raw)
    if first_line == "unknown":
        return CheckResult("unknown", raw=raw)
    return CheckResult("error", raw=raw)


def parse_program(path: Path) -> Program:
    text = path.read_text(encoding="utf-8")
    program = Parser(tokenize(text), path).parse()
    return dataclasses.replace(program, title=extract_title(text, path))


def extract_title(text: str, path: Path) -> str:
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            title = stripped.lstrip("#").strip()
            if title:
                return title
        if stripped.startswith("//"):
            title = stripped.removeprefix("//").strip()
            if title:
                return title
        break
    return path.stem.replace("_", " ").title()


def fill_missing_invariants(program: Program) -> Program:
    def fill_block(stmts: list[Stmt]) -> list[Stmt]:
        filled: list[Stmt] = []
        for stmt in stmts:
            if isinstance(stmt, If):
                filled.append(
                    dataclasses.replace(
                        stmt,
                        then_body=fill_block(stmt.then_body),
                        else_body=fill_block(stmt.else_body),
                    )
                )
            elif isinstance(stmt, While):
                invariant = stmt.invariant or guess_loop_invariant(stmt, program.post)
                if invariant is None:
                    raise HoareError(
                        f"{program.path}:{stmt.line}: loop has no invariant. "
                        "Add `invariant { ... }` after the while condition."
                    )
                filled.append(dataclasses.replace(stmt, invariant=invariant, body=fill_block(stmt.body)))
            else:
                filled.append(stmt)
        return filled

    return dataclasses.replace(program, body=fill_block(program.body))


def guess_loop_invariant(stmt: While, post: Expr) -> Expr | None:
    """Infer the common binary-search range invariant.

    This is deliberately narrow.  General invariant inference is undecidable; the
    heuristic only handles loops shaped like `while lo < hi` with final post
    `lo == target`, producing `lo <= target && target <= hi`.
    """

    if not (
        isinstance(stmt.cond, Binary)
        and stmt.cond.op == "<"
        and isinstance(stmt.cond.left, Var)
        and isinstance(stmt.cond.right, Var)
    ):
        return None
    lo = stmt.cond.left
    hi = stmt.cond.right
    target = target_from_equality(post, lo.name)
    if target is None or target.name == hi.name:
        return None
    return mk_and([Binary("<=", lo, target), Binary("<=", target, hi)])


def target_from_equality(expr: Expr, name: str) -> Var | None:
    for conjunct in flatten_and(expr):
        if not (isinstance(conjunct, Binary) and conjunct.op == "=="):
            continue
        if isinstance(conjunct.left, Var) and conjunct.left.name == name and isinstance(conjunct.right, Var):
            return conjunct.right
        if isinstance(conjunct.right, Var) and conjunct.right.name == name and isinstance(conjunct.left, Var):
            return conjunct.left
    return None


def flatten_and(expr: Expr) -> list[Expr]:
    if isinstance(expr, Binary) and expr.op == "&&":
        return flatten_and(expr.left) + flatten_and(expr.right)
    return [expr]


def verify(program: Program, z3_path: str, timeout: float, show_smt: bool) -> tuple[list[VC], dict[str, CheckResult]]:
    program = fill_missing_invariants(program)
    types = infer_types(program)
    vcs: list[VC] = []
    pre_wp = wp_block(program.body, program.post, vcs)
    vcs.insert(
        0,
        VC(
            name="precondition establishes program weakest precondition",
            expr=mk_implies(program.pre, pre_wp),
            rule="Consequence + structural WP",
            premise=f"precondition implies wp(program, post): {pre_wp.to_source()}",
            line=1,
        ),
    )

    if show_smt:
        for vc in vcs:
            print(f";; {program.path}:{vc.line}: {vc.name}")
            print(smt_script(vc.expr, types))

    results: dict[str, CheckResult] = {}
    for vc in vcs:
        results[vc.name] = run_z3(vc.expr, types, z3_path, timeout)
    return vcs, results


def print_report(program: Program, vcs: list[VC], results: dict[str, CheckResult], verbose: bool) -> bool:
    print(f"\n== {program.path} ==")
    all_valid = True
    for index, vc in enumerate(vcs, start=1):
        result = results[vc.name]
        marker = {
            "valid": "valid",
            "invalid": "invalid",
            "unknown": "unknown",
            "timeout": "timeout",
            "error": "error",
        }[result.status]
        print(f"[{marker}] VC {index}: {vc.name}")
        print(f"        rule: {vc.rule}")
        if verbose:
            print(f"     premise: {vc.premise}")
            print(f"     formula: {vc.expr.to_source()}")
        if result.status == "invalid" and result.model:
            print("       model:")
            for line in result.model.splitlines():
                print(f"         {line}")
        elif result.status in {"unknown", "error"} and result.raw:
            print(f"         z3: {result.raw}")
        if result.status != "valid":
            all_valid = False
    print(f"summary: {sum(1 for r in results.values() if r.status == 'valid')}/{len(vcs)} VCs valid")
    return all_valid


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


def pretty_expr(expr: Expr, parent_prec: int = 0) -> str:
    if isinstance(expr, IntLit):
        return str(expr.value)
    if isinstance(expr, BoolLit):
        return "true" if expr.value else "false"
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Unary):
        if expr.op == "!":
            inner = pretty_expr(expr.expr, 8)
            if isinstance(expr.expr, Binary):
                inner = f"({pretty_expr(expr.expr)})"
            return f"!{inner}"
        if expr.op == "-":
            inner = pretty_expr(expr.expr, 8)
            if isinstance(expr.expr, Binary):
                inner = f"({pretty_expr(expr.expr)})"
            return f"-{inner}"
    if isinstance(expr, Binary):
        if expr.op == "&&":
            text = " && ".join(pretty_expr(part, PREC["&&"]) for part in flatten_and(expr))
            return f"({text})" if PREC["&&"] < parent_prec else text
        op = expr.op
        prec = PREC[op]
        left = pretty_expr(expr.left, prec)
        right_parent = prec if op == "=>" else prec + 1
        right = pretty_expr(expr.right, right_parent)
        text = f"{left} {op} {right}"
        return f"({text})" if prec < parent_prec else text
    raise HoareError(f"cannot pretty-print expression: {expr!r}")


def stmt_wp_for_annotation(stmt: Stmt, post: Expr) -> Expr:
    if isinstance(stmt, Skip):
        return post
    if isinstance(stmt, Assign):
        return post.subst(stmt.name, stmt.expr)
    if isinstance(stmt, Assert):
        return stmt.expr
    if isinstance(stmt, If):
        inferred = infer_if_precondition(stmt, post)
        if inferred is not None:
            return inferred
        then_wp = annotation_block_pre(stmt.then_body, post)
        else_wp = annotation_block_pre(stmt.else_body, post)
        return mk_and([mk_implies(stmt.cond, then_wp), mk_implies(mk_not(stmt.cond), else_wp)])
    if isinstance(stmt, While):
        if stmt.invariant is None:
            raise HoareError(f"loop at line {stmt.line} has no invariant")
        return stmt.invariant
    raise HoareError(f"unknown statement: {stmt!r}")


def annotation_block_pre(stmts: list[Stmt], post: Expr) -> Expr:
    current = post
    for stmt in reversed(stmts):
        current = stmt_wp_for_annotation(stmt, current)
    return current


def annotation_pairs(stmts: list[Stmt], post: Expr) -> list[tuple[Stmt, Expr, Expr]]:
    pairs_reversed: list[tuple[Stmt, Expr, Expr]] = []
    current = post
    for stmt in reversed(stmts):
        pre = stmt_wp_for_annotation(stmt, current)
        pairs_reversed.append((stmt, pre, current))
        current = pre
    return list(reversed(pairs_reversed))


def infer_if_precondition(stmt: If, post: Expr) -> Expr | None:
    """Choose a readable strengthening for the binary-search branch split."""

    range_vars = extract_range(post)
    if range_vars is None:
        return None
    lo, target, hi = range_vars
    if not (
        isinstance(stmt.cond, Binary)
        and stmt.cond.op == "<"
        and isinstance(stmt.cond.left, Var)
        and isinstance(stmt.cond.right, Var)
        and stmt.cond.right.name == target.name
    ):
        return None
    mid = stmt.cond.left
    if len(stmt.then_body) != 1 or len(stmt.else_body) != 1:
        return None
    then_stmt = stmt.then_body[0]
    else_stmt = stmt.else_body[0]
    if not (
        isinstance(then_stmt, Assign)
        and then_stmt.name == lo.name
        and is_plus_one(then_stmt.expr, mid.name)
        and isinstance(else_stmt, Assign)
        and else_stmt.name == hi.name
        and isinstance(else_stmt.expr, Var)
        and else_stmt.expr.name == mid.name
    ):
        return None
    return mk_and([post, Binary("<=", lo, mid), Binary("<", mid, hi)])


def extract_range(expr: Expr) -> tuple[Var, Var, Var] | None:
    conjuncts = flatten_and(expr)
    for left_bound in conjuncts:
        if not (
            isinstance(left_bound, Binary)
            and left_bound.op == "<="
            and isinstance(left_bound.left, Var)
            and isinstance(left_bound.right, Var)
        ):
            continue
        lo = left_bound.left
        target = left_bound.right
        for right_bound in conjuncts:
            if (
                isinstance(right_bound, Binary)
                and right_bound.op == "<="
                and isinstance(right_bound.left, Var)
                and right_bound.left.name == target.name
                and isinstance(right_bound.right, Var)
            ):
                return lo, target, right_bound.right
    return None


def is_plus_one(expr: Expr, name: str) -> bool:
    return (
        isinstance(expr, Binary)
        and expr.op == "+"
        and isinstance(expr.left, Var)
        and expr.left.name == name
        and isinstance(expr.right, IntLit)
        and expr.right.value == 1
    )


def render_solution(program: Program, comments: bool = True) -> str:
    program = fill_missing_invariants(program)
    lines: list[str] = []
    title = program.title or program.path.stem.replace("_", " ").title()
    lines.append(f"# {title}")
    lines.append("# Solution")
    append_assertion(
        lines,
        0,
        program.pre,
        "Precondition",
        "given by the Hoare triple.",
        comments,
    )
    render_block(lines, program.body, program.pre, program.post, 0, comments, force_first=True)
    return "\n".join(lines)


def render_block(
    lines: list[str],
    stmts: list[Stmt],
    incoming: Expr,
    outgoing: Expr,
    indent: int,
    comments: bool,
    force_first: bool = False,
) -> None:
    current = incoming
    pairs = annotation_pairs(stmts, outgoing)
    for index, (stmt, pre, post) in enumerate(pairs):
        if pre != current:
            append_assertion(
                lines,
                indent,
                current,
                "Sequence",
                "this is the postcondition established by the previous command.",
                comments,
            )
            append_assertion(
                lines,
                indent,
                pre,
                "Consequence",
                f"strengthen/weaken the current assertion to the rule precondition; prove {pretty_expr(current)} => {pretty_expr(pre)}.",
                comments,
            )
        elif index == 0 and force_first:
            append_assertion(
                lines,
                indent,
                pre,
                "Sequence",
                "the first command starts from the current precondition.",
                comments,
            )

        render_stmt(lines, stmt, pre, post, indent, comments)
        current = post


def render_stmt(lines: list[str], stmt: Stmt, pre: Expr, post: Expr, indent: int, comments: bool) -> None:
    pad = " " * indent
    if isinstance(stmt, Assign):
        lines.append(f"{pad}{stmt.name} := {pretty_expr(stmt.expr)}")
        append_assertion(
            lines,
            indent,
            post,
            "Assignment",
            f"assignment axiom with Q = {pretty_expr(post)}; required precondition is Q[{stmt.name} := {pretty_expr(stmt.expr)}] = {pretty_expr(pre)}.",
            comments,
        )
        return

    if isinstance(stmt, Skip):
        lines.append(f"{pad}skip")
        append_assertion(lines, indent, post, "Skip", "skip preserves the assertion.", comments)
        return

    if isinstance(stmt, Assert):
        append_assertion(
            lines,
            indent,
            stmt.expr,
            "Consequence / annotation",
            f"inserted assertion must imply the next weakest precondition {pretty_expr(post)}.",
            comments,
        )
        return

    if isinstance(stmt, If):
        lines.append(f"{pad}if {pretty_expr(stmt.cond)} then")
        then_incoming = mk_and([pre, stmt.cond])
        render_block(lines, stmt.then_body, then_incoming, post, indent + 4, comments, force_first=True)
        lines.append(f"{pad}else")
        else_incoming = mk_and([pre, mk_not(stmt.cond)])
        render_block(lines, stmt.else_body, else_incoming, post, indent + 4, comments, force_first=True)
        lines.append(f"{pad}fi")
        append_assertion(
            lines,
            indent,
            post,
            "If",
            "both branches establish the same postcondition.",
            comments,
        )
        return

    if isinstance(stmt, While):
        if stmt.invariant is None:
            raise HoareError(f"loop at line {stmt.line} has no invariant")
        lines.append(f"{pad}while {pretty_expr(stmt.cond)} do")
        body_incoming = mk_and([stmt.invariant, stmt.cond])
        render_block(lines, stmt.body, body_incoming, stmt.invariant, indent + 4, comments, force_first=True)
        lines.append(f"{pad}od")
        loop_exit = mk_and([stmt.invariant, mk_not(stmt.cond)])
        append_assertion(
            lines,
            indent,
            loop_exit,
            "While",
            "after the loop exits, the invariant holds and the guard is false.",
            comments,
        )
        if post != loop_exit:
            append_assertion(
                lines,
                indent,
                post,
                "Consequence",
                f"prove {pretty_expr(loop_exit)} => {pretty_expr(post)}.",
                comments,
            )
        return

    raise HoareError(f"unknown statement: {stmt!r}")


def append_assertion(
    lines: list[str],
    indent: int,
    expr: Expr,
    rule: str,
    premise: str,
    comments: bool,
) -> None:
    pad = " " * indent
    if comments:
        lines.append(f"{pad}# Rule: {rule}")
        lines.append(f"{pad}# Premise: {premise}")
    lines.append(f"{pad}{{{pretty_expr(expr)}}}")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description="Verify annotated textbook Hoare-logic programs with Z3.")
    parser.add_argument("files", nargs="+", type=Path, help="one or more .hl files")
    parser.add_argument("--z3", default=shutil.which("z3") or "z3", help="path to z3 executable")
    parser.add_argument("--timeout", type=float, default=10.0, help="per-VC solver timeout in seconds")
    parser.add_argument("--verbose", action="store_true", help="print premises and formulas")
    parser.add_argument("--show-smt", action="store_true", help="print SMT-LIB generated for each VC")
    parser.add_argument("--annotate", action="store_true", help="print a lecture-style annotated solution")
    parser.add_argument("--no-annotation-comments", action="store_true", help="omit rule/premise comments in --annotate output")
    args = parser.parse_args(argv)

    if not shutil.which(args.z3) and not Path(args.z3).exists():
        raise HoareError(f"Z3 executable not found: {args.z3}")

    ok = True
    for path in args.files:
        program = parse_program(path)
        if args.annotate:
            print(render_solution(program, comments=not args.no_annotation_comments))
        else:
            vcs, results = verify(program, args.z3, args.timeout, args.show_smt)
            ok = print_report(program, vcs, results, args.verbose) and ok
    return 0 if ok else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except HoareError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
