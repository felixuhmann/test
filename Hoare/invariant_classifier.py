#!/usr/bin/env python3
"""Classify candidate loop invariants with Z3.

This tool is aimed at worksheet-style questions:

* "inductive invariant" means initialized at the loop head and preserved by one
  loop-body step from every state satisfying the candidate and the guard.
* "non-inductive invariant" means the candidate holds on reachable loop-head
  states, but the one-step preservation Hoare triple fails.
* "neither" means a reachable loop-head state falsifies the candidate.

General invariant discovery is undecidable, so the tool uses three layers:

1. exact Z3 checks for initialization and preservation;
2. bounded symbolic unrolling to find reachable counterexamples;
3. optional `reachable { ... }` facts, themselves checked as inductive, to prove
   that non-inductive candidates are still invariants.
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

from hoare_solver import (
    Assign,
    Binary,
    BoolLit,
    Expr,
    HoareError,
    If,
    IntLit,
    Parser,
    Program,
    Skip,
    Stmt,
    Token,
    Unary,
    Var,
    While,
    infer_types,
    mk_and,
    mk_implies,
    mk_not,
    smt_name,
    tokenize,
    wp_block,
)


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
        return (
            self.cond.variables()
            | self.then_expr.variables()
            | self.else_expr.variables()
        )

    def to_source(self) -> str:
        return (
            f"(if {self.cond.to_source()} then "
            f"{self.then_expr.to_source()} else {self.else_expr.to_source()})"
        )

    def to_smt(self) -> str:
        return (
            f"(ite {self.cond.to_smt()} "
            f"{self.then_expr.to_smt()} {self.else_expr.to_smt()})"
        )


@dataclasses.dataclass
class InvariantProblem:
    declarations: dict[str, str]
    pre: Expr
    init: list[Stmt]
    guard: Expr
    body: list[Stmt]
    candidates: list[Expr]
    reachable: Expr | None
    path: Path


@dataclasses.dataclass
class SolverResult:
    status: str
    raw: str = ""
    values: dict[str, str] = dataclasses.field(default_factory=dict)


@dataclasses.dataclass
class Classification:
    kind: str
    reason: str
    detail: dict[str, str] = dataclasses.field(default_factory=dict)


class ProblemParser(Parser):
    def __init__(self, tokens: list[Token], path: Path):
        super().__init__(tokens, path)
        self.declarations: dict[str, str] = {}

    def parse_problem(self) -> InvariantProblem:
        while self.at("vars"):
            self.parse_invariant_declaration()

        self.expect("pre")
        pre = self.parse_braced_expr()

        self.expect("init")
        init = self.parse_block()

        self.expect("while")
        self.expect("(")
        guard = self.parse_expr()
        self.expect(")")
        body = self.parse_block()

        candidates: list[Expr] = []
        reachable_parts: list[Expr] = []
        while not self.at("eof"):
            if self.match("reachable"):
                reachable_parts.append(self.parse_braced_expr())
            elif self.match("candidate"):
                candidates.append(self.parse_braced_expr())
            else:
                cur = self.current()
                raise HoareError(
                    f"{self.path}:{cur.line}:{cur.col}: "
                    "expected 'reachable', 'candidate', or EOF"
                )

        if not candidates:
            raise HoareError(f"{self.path}: expected at least one candidate")

        reachable = mk_and(reachable_parts) if reachable_parts else None
        return InvariantProblem(
            self.declarations,
            pre,
            init,
            guard,
            body,
            candidates,
            reachable,
            self.path,
        )

    def parse_invariant_declaration(self) -> None:
        self.expect("vars")
        if self.match("int"):
            typ = "Int"
        elif self.match("nat"):
            typ = "Nat"
        elif self.match("bool"):
            typ = "Bool"
        else:
            cur = self.current()
            raise HoareError(f"{self.path}:{cur.line}:{cur.col}: expected int, nat, or bool")

        while True:
            name = self.expect("id").value
            old = self.declarations.get(name)
            if old and old != typ:
                raise HoareError(f"{self.path}: conflicting declarations for {name}")
            self.declarations[name] = typ
            if not self.match(","):
                break
        self.expect(";")


def parse_invariant_problem(path: Path) -> InvariantProblem:
    text = path.read_text(encoding="utf-8")
    return ProblemParser(tokenize(text), path).parse_problem()


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
    raise HoareError(f"unsupported expression: {expr!r}")


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
    if isinstance(stmt, While):
        raise HoareError("nested while loops are not supported by the classifier")
    raise HoareError(f"unsupported statement in classifier: {stmt!r}")


def smt_types(types: dict[str, str]) -> dict[str, str]:
    return {name: ("Int" if typ == "Nat" else typ) for name, typ in types.items()}


def domain_expr(types: dict[str, str], state: dict[str, Expr] | None = None) -> Expr:
    parts: list[Expr] = []
    for name, typ in sorted(types.items()):
        if typ == "Nat":
            term = state[name] if state and name in state else Var(name)
            parts.append(Binary(">=", term, IntLit(0)))
    return mk_and(parts)


def infer_problem_types(problem: InvariantProblem) -> dict[str, str]:
    declared_for_hoare = {
        name: ("Int" if typ == "Nat" else typ)
        for name, typ in problem.declarations.items()
    }
    post_parts = [problem.guard, *problem.candidates]
    if problem.reachable is not None:
        post_parts.append(problem.reachable)

    program = Program(
        declared_for_hoare,
        problem.pre,
        [*problem.init, While(0, problem.guard, BoolLit(True), problem.body)],
        mk_and(post_parts),
        problem.path,
    )
    inferred = infer_types(program)
    return {
        name: (problem.declarations[name] if name in problem.declarations else typ)
        for name, typ in inferred.items()
    }


def declarations_smt(types: dict[str, str]) -> str:
    return "\n".join(
        f"(declare-const {smt_name(name)} {typ})"
        for name, typ in sorted(smt_types(types).items())
    )


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
        raise HoareError("unexpected end of S-expression")
    token = tokens[pos]
    if token != "(":
        return token, pos + 1
    pos += 1
    items: list[object] = []
    while pos < len(tokens) and tokens[pos] != ")":
        item, pos = parse_one_sexpr(tokens, pos)
        items.append(item)
    if pos >= len(tokens):
        raise HoareError("unterminated S-expression")
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


def check_sat_with_values(
    condition: Expr,
    types: dict[str, str],
    value_exprs: list[tuple[str, str, Expr]],
    z3_path: str,
    timeout: float,
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
            f"(assert {condition.to_smt()})",
            *alias_decls,
            *alias_asserts,
            "(check-sat)",
            f"(get-value ({' '.join(smt_name(name) for name in value_names)}))",
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


def implication(antecedent: Expr, consequent: Expr) -> Expr:
    return mk_implies(antecedent, consequent)


def initialized_vc(problem: InvariantProblem, formula: Expr, types: dict[str, str]) -> Expr:
    vcs: list[object] = []
    loop_head_formula = wp_block(problem.init, formula, vcs)  # type: ignore[arg-type]
    return implication(mk_and([domain_expr(types), problem.pre]), loop_head_formula)


def preservation_vc(problem: InvariantProblem, formula: Expr, types: dict[str, str]) -> Expr:
    vcs: list[object] = []
    body_wp = wp_block(problem.body, formula, vcs)  # type: ignore[arg-type]
    return implication(
        mk_and([domain_expr(types), formula, problem.guard]),
        body_wp,
    )


def preservation_counterexample_condition(
    problem: InvariantProblem, formula: Expr, types: dict[str, str]
) -> Expr:
    vcs: list[object] = []
    body_wp = wp_block(problem.body, formula, vcs)  # type: ignore[arg-type]
    return mk_and([domain_expr(types), formula, problem.guard, mk_not(body_wp)])


def init_counterexample_condition(
    problem: InvariantProblem, formula: Expr, types: dict[str, str]
) -> Expr:
    vcs: list[object] = []
    loop_head_formula = wp_block(problem.init, formula, vcs)  # type: ignore[arg-type]
    return mk_and([domain_expr(types), problem.pre, mk_not(loop_head_formula)])


def sorted_variables(types: dict[str, str]) -> list[str]:
    return sorted(types)


def displayed_variables(problem: InvariantProblem, types: dict[str, str]) -> list[str]:
    names = set(problem.guard.variables())
    for stmt in problem.body:
        names |= stmt.variables()
    for candidate in problem.candidates:
        names |= candidate.variables()
    if problem.reachable is not None:
        names |= problem.reachable.variables()
    return sorted(name for name in names if name in types)


def value_terms_for_state(
    prefix: str,
    state: dict[str, Expr],
    types: dict[str, str],
    variables: list[str],
) -> list[tuple[str, str, Expr]]:
    return [
        (f"{prefix}_{name}", types[name], state.get(name, Var(name)))
        for name in variables
        if types[name] in {"Int", "Nat", "Bool"}
    ]


def find_reachable_counterexample(
    problem: InvariantProblem,
    formula: Expr,
    types: dict[str, str],
    execution_variables: list[str],
    output_variables: list[str],
    unroll: int,
    z3_path: str,
    timeout: float,
) -> tuple[int, SolverResult] | None:
    state = {name: Var(name) for name in execution_variables}
    state = symbolic_execute(problem.init, state, execution_variables)
    path_conditions: list[Expr] = []

    for iteration in range(unroll + 1):
        formula_here = subst_map(formula, state)
        condition = mk_and(
            [
                domain_expr(types),
                problem.pre,
                *path_conditions,
                mk_not(formula_here),
            ]
        )
        result = check_sat_with_values(
            condition,
            types,
            value_terms_for_state("state", state, types, output_variables),
            z3_path,
            timeout,
        )
        if result.status == "sat":
            return iteration, result
        if result.status not in {"unsat"}:
            return iteration, result

        guard_here = subst_map(problem.guard, state)
        path_conditions.append(guard_here)
        state = symbolic_execute(problem.body, state, execution_variables)
    return None


def prove_with_reachable_fact(
    problem: InvariantProblem,
    formula: Expr,
    types: dict[str, str],
    z3_path: str,
    timeout: float,
) -> tuple[bool, str]:
    if problem.reachable is None:
        return False, "no reachable fact supplied"

    fact_init = check_valid(initialized_vc(problem, problem.reachable, types), types, z3_path, timeout)
    if fact_init.status != "valid":
        return False, f"reachable fact is not initialized ({fact_init.status})"

    fact_pres = check_valid(preservation_vc(problem, problem.reachable, types), types, z3_path, timeout)
    if fact_pres.status != "valid":
        return False, f"reachable fact is not preserved ({fact_pres.status})"

    implies_candidate = check_valid(
        implication(mk_and([domain_expr(types), problem.reachable]), formula),
        types,
        z3_path,
        timeout,
    )
    if implies_candidate.status != "valid":
        return False, f"reachable fact does not imply candidate ({implies_candidate.status})"

    return True, "reachable fact is initialized, preserved, and implies the candidate"


def classify_candidate(
    problem: InvariantProblem,
    formula: Expr,
    types: dict[str, str],
    execution_variables: list[str],
    output_variables: list[str],
    unroll: int,
    z3_path: str,
    timeout: float,
) -> Classification:
    init = check_valid(initialized_vc(problem, formula, types), types, z3_path, timeout)
    if init.status != "valid":
        loop_state = symbolic_execute(
            problem.init,
            {name: Var(name) for name in execution_variables},
            execution_variables,
        )
        result = check_sat_with_values(
            init_counterexample_condition(problem, formula, types),
            types,
            value_terms_for_state("state", loop_state, types, output_variables),
            z3_path,
            timeout,
        )
        return Classification(
            "Neither",
            "candidate is false at an initial loop-head state",
            result.values,
        )

    pres = check_valid(preservation_vc(problem, formula, types), types, z3_path, timeout)
    if pres.status == "valid":
        return Classification(
            "Inductive invariant",
            "candidate is initialized and preserved by the loop body",
        )

    reachable_counterexample = find_reachable_counterexample(
        problem,
        formula,
        types,
        execution_variables,
        output_variables,
        unroll,
        z3_path,
        timeout,
    )
    if reachable_counterexample is not None:
        iteration, result = reachable_counterexample
        if result.status == "sat":
            values = {"iterations": str(iteration), **result.values}
            return Classification(
                "Neither",
                f"candidate is false at a reachable loop-head state after {iteration} iteration(s)",
                values,
            )
        return Classification(
            "Unknown",
            f"reachable-state search returned {result.status}",
            {"z3": result.raw},
        )

    proved, proof_reason = prove_with_reachable_fact(problem, formula, types, z3_path, timeout)
    if proved:
        before_state = {name: Var(name) for name in execution_variables}
        after_state = symbolic_execute(problem.body, before_state, execution_variables)
        result = check_sat_with_values(
            preservation_counterexample_condition(problem, formula, types),
            types,
            [
                *value_terms_for_state("before", before_state, types, output_variables),
                *value_terms_for_state("after", after_state, types, output_variables),
            ],
            z3_path,
            timeout,
        )
        return Classification(
            "Non-inductive invariant",
            f"{proof_reason}; one-step preservation fails",
            result.values,
        )

    return Classification(
        "Unknown",
        (
            "candidate is initialized but not inductive; no reachable counterexample "
            f"was found up to {unroll} iteration(s), and invariance was not proved"
        ),
    )


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
    problem: InvariantProblem,
    classifications: list[tuple[Expr, Classification]],
    reachable_status: str | None,
) -> None:
    print(f"\n== {problem.path} ==")
    if reachable_status:
        print(f"reachable fact: {reachable_status}")
    for index, (formula, classification) in enumerate(classifications, start=1):
        print(f"[{classification.kind}] candidate {index}: {formula.to_source()}")
        print(f"    reason: {classification.reason}")
        print_values(classification.detail)


def reachable_fact_status(
    problem: InvariantProblem,
    types: dict[str, str],
    z3_path: str,
    timeout: float,
) -> str | None:
    if problem.reachable is None:
        return None
    init = check_valid(initialized_vc(problem, problem.reachable, types), types, z3_path, timeout)
    pres = check_valid(preservation_vc(problem, problem.reachable, types), types, z3_path, timeout)
    return f"initialized={init.status}, preserved={pres.status}: {problem.reachable.to_source()}"


def solve_file(path: Path, args: argparse.Namespace) -> bool:
    problem = parse_invariant_problem(path)
    types = infer_problem_types(problem)
    execution_variables = sorted_variables(types)
    output_variables = displayed_variables(problem, types)
    classifications = [
        (
            candidate,
            classify_candidate(
                problem,
                candidate,
                types,
                execution_variables,
                output_variables,
                args.unroll,
                args.z3,
                args.timeout,
            ),
        )
        for candidate in problem.candidates
    ]
    print_problem_report(
        problem,
        classifications,
        reachable_fact_status(problem, types, args.z3, args.timeout),
    )
    return all(classification.kind != "Unknown" for _, classification in classifications)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Classify worksheet-style candidate loop invariants with Z3."
    )
    parser.add_argument("files", nargs="+", type=Path, help="one or more .inv files")
    parser.add_argument("--z3", default=shutil.which("z3") or "z3", help="path to z3 executable")
    parser.add_argument(
        "--unroll",
        type=int,
        default=20,
        help="bounded iterations used to find reachable counterexamples",
    )
    parser.add_argument("--timeout", type=float, default=10.0, help="per-query Z3 timeout")
    args = parser.parse_args(argv)

    if not shutil.which(args.z3) and not Path(args.z3).exists():
        raise HoareError(f"Z3 executable not found: {args.z3}")

    ok = True
    for path in args.files:
        ok = solve_file(path, args) and ok
    return 0 if ok else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except HoareError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
