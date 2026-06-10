#!/usr/bin/env python3
"""
Find a strong mutation-killing test for two one-function C files.

The original and mutant must have compatible primitive parameter lists and the
same non-void return type. The script reports an input for which the return
values differ.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pycparser import c_ast, c_generator

from coverage_check import (
    PARSER_PREFIX_LINES,
    function_name,
    function_parameters,
    load_cases,
    normalize_type_name,
    parse_c_file,
    value_to_c_literal,
)
from suggest_tests import (
    case_to_c_args,
    default_domain,
    function_return_type,
    generate_candidate_cases,
    is_bool_type,
    is_float_type,
    is_unsigned_type,
    is_void_type,
    load_domain,
    unique_case_list,
)


ORIGINAL_NAME = "__kill_original"
MUTANT_NAME = "__kill_mutant"


@dataclass(frozen=True)
class KillResult:
    killed: bool
    inputs: list[Any]
    original_output: str
    mutant_output: str
    engine: str
    hints: list[str]


def clone_with_name(function: c_ast.FuncDef, new_name: str) -> c_ast.FuncDef:
    old_name = function.decl.name
    function.decl.name = new_name
    rename_declname(function.decl.type, new_name)
    rename_recursive_calls(function, old_name, new_name)
    return function


def rename_declname(node: c_ast.Node, new_name: str) -> None:
    current = node
    while hasattr(current, "type"):
        if isinstance(current, c_ast.TypeDecl):
            current.declname = new_name
            return
        current = current.type


def rename_recursive_calls(function: c_ast.FuncDef, old_name: str, new_name: str) -> None:
    class Renamer(c_ast.NodeVisitor):
        def visit_FuncCall(self, node: c_ast.FuncCall) -> None:
            if isinstance(node.name, c_ast.ID) and node.name.name == old_name:
                node.name.name = new_name
            self.generic_visit(node)

    Renamer().visit(function.body)


def compatible_signatures(original: c_ast.FuncDef, mutant: c_ast.FuncDef) -> tuple[list[Any], str]:
    original_parameters = function_parameters(original)
    mutant_parameters = function_parameters(mutant)
    if len(original_parameters) != len(mutant_parameters):
        raise SystemExit(
            f"Parameter count mismatch: original has {len(original_parameters)}, mutant has {len(mutant_parameters)}."
        )
    for index, (original_param, mutant_param) in enumerate(zip(original_parameters, mutant_parameters), start=1):
        if normalize_type_name(original_param.type_name) != normalize_type_name(mutant_param.type_name):
            raise SystemExit(
                "Parameter type mismatch at position "
                f"{index}: original has {original_param.type_name!r}, mutant has {mutant_param.type_name!r}."
            )

    original_return = function_return_type(original)
    mutant_return = function_return_type(mutant)
    if normalize_type_name(original_return) != normalize_type_name(mutant_return):
        raise SystemExit(f"Return type mismatch: original {original_return!r}, mutant {mutant_return!r}.")
    if is_void_type(original_return):
        raise SystemExit("Strong killing by return value is not defined for void functions.")
    return original_parameters, original_return


def render_functions(original: c_ast.FuncDef, mutant: c_ast.FuncDef) -> str:
    generator = c_generator.CGenerator()
    return generator.visit(original) + "\n" + generator.visit(mutant) + "\n"


def output_format(return_type: str, var_name: str) -> tuple[str, list[str]]:
    if is_bool_type(return_type):
        return "%s", [f"{var_name} ? \"true\" : \"false\""]
    if is_float_type(return_type):
        return "%.17Lg", [f"(long double){var_name}"]
    if is_unsigned_type(return_type):
        return "%llu", [f"(unsigned long long){var_name}"]
    return "%lld", [f"(long long){var_name}"]


def inequality_expression(return_type: str, left: str, right: str) -> str:
    if is_float_type(return_type):
        return f"(({left}) != ({right}))"
    return f"(({left}) != ({right}))"


def generate_execution_harness(
    rendered_functions: str,
    return_type: str,
    parameters: list[Any],
    cases: list[list[Any]],
) -> str:
    lines = [
        "#include <stdbool.h>",
        "#include <stddef.h>",
        "#include <stdint.h>",
        "#include <stdio.h>",
        "#include <limits.h>",
        "#include <float.h>",
        "",
        rendered_functions,
        "int main(void) {",
    ]
    original_fmt, original_args = output_format(return_type, "__kill_o")
    mutant_fmt, mutant_args = output_format(return_type, "__kill_m")
    for index, case in enumerate(cases):
        args = case_to_c_args(case, parameters)
        lines.extend(
            [
                "    {",
                f"        {return_type} __kill_o = {ORIGINAL_NAME}({args});",
                f"        {return_type} __kill_m = {MUTANT_NAME}({args});",
                f"        if ({inequality_expression(return_type, '__kill_o', '__kill_m')}) {{",
                (
                    f"            printf(\"K {index} {original_fmt} {mutant_fmt}\\n\", "
                    + ", ".join(original_args + mutant_args)
                    + ");"
                ),
                "        }",
                "    }",
            ]
        )
    lines.extend(["    return 0;", "}", ""])
    return "\n".join(lines)


def generate_indexed_execution_harness(
    rendered_functions: str,
    return_type: str,
    parameters: list[Any],
    cases: list[list[Any]],
) -> str:
    lines = [
        "#include <stdbool.h>",
        "#include <stddef.h>",
        "#include <stdint.h>",
        "#include <stdio.h>",
        "#include <stdlib.h>",
        "#include <limits.h>",
        "#include <float.h>",
        "",
        rendered_functions,
        "int main(int argc, char **argv) {",
        "    int __kill_case = argc > 1 ? atoi(argv[1]) : 0;",
        "    switch (__kill_case) {",
    ]
    original_fmt, original_args = output_format(return_type, "__kill_o")
    mutant_fmt, mutant_args = output_format(return_type, "__kill_m")
    for index, case in enumerate(cases):
        args = case_to_c_args(case, parameters)
        lines.extend(
            [
                f"    case {index}:",
                "        {",
                f"            {return_type} __kill_o = {ORIGINAL_NAME}({args});",
                f"            {return_type} __kill_m = {MUTANT_NAME}({args});",
                f"            if ({inequality_expression(return_type, '__kill_o', '__kill_m')}) {{",
                (
                    f"                printf(\"K {index} {original_fmt} {mutant_fmt}\\n\", "
                    + ", ".join(original_args + mutant_args)
                    + ");"
                ),
                "            }",
                "            break;",
                "        }",
            ]
        )
    lines.extend(
        [
            "    default:",
            "        return 2;",
            "    }",
            "    return 0;",
            "}",
            "",
        ]
    )
    return "\n".join(lines)


def compile_source(source: str, build_dir: Path, stem: str) -> Path:
    generated_c = build_dir / f"{stem}.c"
    binary = build_dir / stem
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
    return binary


def compile_and_run(source: str, build_dir: Path, stem: str, timeout: float) -> str:
    binary = compile_source(source, build_dir, stem)
    try:
        run_result = subprocess.run([str(binary)], text=True, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        raise SystemExit(f"Execution timed out after {timeout} seconds.") from exc
    if run_result.returncode != 0:
        raise SystemExit(
            "Execution failed.\n"
            f"stdout:\n{run_result.stdout}\n"
            f"stderr:\n{run_result.stderr}"
        )
    return run_result.stdout


def parse_kill_output(output: str, cases: list[list[Any]], engine: str) -> KillResult | None:
    for line in output.splitlines():
        if not line.startswith("K "):
            continue
        parts = line.split(maxsplit=3)
        if len(parts) < 4:
            continue
        index = int(parts[1])
        original_output, mutant_output = parts[2], parts[3]
        return KillResult(
            killed=True,
            inputs=cases[index],
            original_output=original_output,
            mutant_output=mutant_output,
            engine=engine,
            hints=[],
        )
    return None


def bounded_search(
    rendered_functions: str,
    return_type: str,
    parameters: list[Any],
    cases: list[list[Any]],
    timeout: float,
    keep: bool,
    max_timeouts: int,
) -> tuple[KillResult | None, Path | None, int, bool]:
    harness = generate_indexed_execution_harness(rendered_functions, return_type, parameters, cases)
    if keep:
        build_dir = Path(".kill_mutant_build")
        if build_dir.exists():
            shutil.rmtree(build_dir)
        build_dir.mkdir(parents=True)
        binary = compile_source(harness, build_dir, "kill_mutant_bounded")
        kept_dir: Path | None = build_dir
    else:
        tmpdir = tempfile.TemporaryDirectory(prefix="kill_mutant_")
        build_dir = Path(tmpdir.name)
        binary = compile_source(harness, build_dir, "kill_mutant_bounded")
        kept_dir = None

    try:
        timeout_count = 0
        for index in range(len(cases)):
            try:
                run_result = subprocess.run(
                    [str(binary), str(index)],
                    text=True,
                    capture_output=True,
                    timeout=timeout,
                )
            except subprocess.TimeoutExpired:
                timeout_count += 1
                if timeout_count >= max_timeouts:
                    return None, kept_dir, timeout_count, True
                continue
            if run_result.returncode != 0:
                continue
            result = parse_kill_output(run_result.stdout, cases, "bounded")
            if result is not None:
                return result, kept_dir, timeout_count, False
        return None, kept_dir, timeout_count, False
    finally:
        if not keep:
            tmpdir.cleanup()


def cbmc_nondet_decl(index: int, type_name: str) -> str:
    return f"{type_name} __kill_nondet_{index}(void);"


def cbmc_domain_assumption(parameter_name: str, type_name: str, values: list[Any]) -> str:
    checks = [
        f"({parameter_name} == ({type_name})({value_to_c_literal(value, type_name)}))"
        for value in values
    ]
    if not checks:
        return ""
    return "__CPROVER_assume(" + " || ".join(checks) + ");"


def generate_cbmc_harness(
    rendered_functions: str,
    return_type: str,
    parameters: list[Any],
    domain: dict[str, list[Any]],
) -> str:
    lines = [
        "#include <stdbool.h>",
        "#include <stddef.h>",
        "#include <stdint.h>",
        "#include <limits.h>",
        "#include <float.h>",
        "",
    ]
    for index, parameter in enumerate(parameters):
        lines.append(cbmc_nondet_decl(index, parameter.type_name))
    lines.extend(
        [
            "",
            rendered_functions,
            "int main(void) {",
        ]
    )
    arg_names = []
    for index, parameter in enumerate(parameters):
        arg_name = f"__kill_arg_{index}_{parameter.name}"
        arg_names.append(arg_name)
        lines.append(f"    {parameter.type_name} {arg_name} = __kill_nondet_{index}();")
        if parameter.name in domain:
            assumption = cbmc_domain_assumption(arg_name, parameter.type_name, domain[parameter.name])
            if assumption:
                lines.append(f"    {assumption}")
    joined_args = ", ".join(arg_names)
    lines.extend(
        [
            f"    {return_type} __kill_o = {ORIGINAL_NAME}({joined_args});",
            f"    {return_type} __kill_m = {MUTANT_NAME}({joined_args});",
            f"    __CPROVER_assert(!{inequality_expression(return_type, '__kill_o', '__kill_m')}, \"mutant survives\");",
            "    return 0;",
            "}",
            "",
        ]
    )
    return "\n".join(lines)


def run_cbmc(
    rendered_functions: str,
    return_type: str,
    parameters: list[Any],
    domain: dict[str, list[Any]],
    unwind: int,
    timeout: float,
    keep: bool,
) -> tuple[list[Any] | None, Path | None, str]:
    harness = generate_cbmc_harness(rendered_functions, return_type, parameters, domain)
    if keep:
        build_dir = Path(".kill_mutant_cbmc")
        if build_dir.exists():
            shutil.rmtree(build_dir)
        build_dir.mkdir(parents=True)
        harness_path = build_dir / "kill_mutant_cbmc.c"
        harness_path.write_text(harness, encoding="utf-8")
        kept_dir: Path | None = build_dir
    else:
        tmpdir = tempfile.TemporaryDirectory(prefix="kill_mutant_cbmc_")
        build_dir = Path(tmpdir.name)
        harness_path = build_dir / "kill_mutant_cbmc.c"
        harness_path.write_text(harness, encoding="utf-8")
        kept_dir = None

    command = [
        "cbmc",
        "--json-ui",
        "--trace",
        "--stop-on-fail",
        "--partial-loops",
        "--unwind",
        str(unwind),
        "--function",
        "main",
        str(harness_path),
    ]
    try:
        result = subprocess.run(command, text=True, capture_output=True, timeout=timeout)
    except FileNotFoundError as exc:
        if not keep:
            tmpdir.cleanup()
        raise RuntimeError("CBMC is not installed or not on PATH.") from exc
    except subprocess.TimeoutExpired as exc:
        if not keep:
            tmpdir.cleanup()
        raise RuntimeError(f"CBMC timed out after {timeout} seconds.") from exc

    output = result.stdout
    if not keep:
        tmpdir.cleanup()

    if result.returncode == 10:
        return extract_cbmc_inputs(output, parameters), kept_dir, output
    if result.returncode == 0:
        return None, kept_dir, output
    raise RuntimeError(f"CBMC failed with exit code {result.returncode}.\n{result.stderr}\n{result.stdout}")


def extract_cbmc_inputs(output: str, parameters: list[Any]) -> list[Any] | None:
    try:
        data = json.loads(output)
    except json.JSONDecodeError:
        return None

    wanted = {
        f"__kill_arg_{index}_{parameter.name}": (index, parameter.type_name)
        for index, parameter in enumerate(parameters)
    }
    values: dict[int, Any] = {}
    for item in data:
        trace = item.get("trace")
        if not isinstance(trace, list):
            continue
        for step in trace:
            lhs = step.get("lhs")
            if lhs not in wanted or "value" not in step:
                continue
            index, type_name = wanted[lhs]
            values[index] = convert_cbmc_value(step["value"].get("data", ""), type_name)
    if len(values) != len(parameters):
        return None
    return [values[index] for index in range(len(parameters))]


def convert_cbmc_value(data: str, type_name: str) -> Any:
    normalized = normalize_type_name(type_name).lower()
    if is_bool_type(type_name):
        return data.lower() in {"1", "1u", "true", "true_bool"}
    if is_float_type(type_name):
        cleaned = data.replace("f", "").replace("F", "")
        try:
            return float(cleaned)
        except ValueError:
            return {"$c": data}
    match = re.search(r"-?\d+", data)
    if match:
        return int(match.group(0))
    if normalized in {"char", "signed char", "unsigned char"} and data:
        return data
    return {"$c": data}


def build_domain(
    parameters: list[Any],
    domain_overrides: dict[str, list[Any]],
    values_per_param: int,
) -> dict[str, list[Any]]:
    domain = {}
    for parameter in parameters:
        values = domain_overrides.get(parameter.name)
        if values is None:
            values = default_domain(parameter.type_name)[:values_per_param]
        domain[parameter.name] = values
    return domain


def load_seed_cases(path: Path | None, parameters: list[Any]) -> list[list[Any]]:
    if path is None:
        return []
    return load_cases(path, parameters)


def result_to_json(result: KillResult, parameters: list[Any]) -> dict[str, Any]:
    return {
        "killed": result.killed,
        "engine": result.engine,
        "inputs": {
            parameter.name: value
            for parameter, value in zip(parameters, result.inputs)
        },
        "case": result.inputs,
        "original_output": result.original_output,
        "mutant_output": result.mutant_output,
        "hints": result.hints,
    }


def print_report(result: KillResult, parameters: list[Any], original_path: Path, mutant_path: Path, kept_dir: Path | None) -> None:
    print(f"Original: {original_path}")
    print(f"Mutant: {mutant_path}")
    if result.killed:
        print("Status: strongly killed")
        print(f"Engine: {result.engine}")
        print("Inputs:")
        for parameter, value in zip(parameters, result.inputs):
            print(f"  {parameter.name}: {json.dumps(value)}")
        print(f"Original output: {result.original_output}")
        print(f"Mutant output: {result.mutant_output}")
        print("cases.json entry:")
        print(f"  {json.dumps(result.inputs)}")
    else:
        print("Status: no killing test found")
        print(f"Engine: {result.engine}")
        for hint in result.hints:
            print(f"Hint: {hint}")
    if kept_dir is not None:
        print(f"Kept generated files in {kept_dir}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Find a strong mutation-killing test case for two one-function C files.")
    parser.add_argument("original", help="Original C file containing exactly one function.")
    parser.add_argument("mutant", help="Mutant C file containing exactly one compatible function.")
    parser.add_argument("--cases", type=Path, help="Optional JSON cases to try first and use as domain hints.")
    parser.add_argument("--domain", type=Path, help="Optional JSON domain keyed by original parameter name.")
    parser.add_argument("--engine", choices=["auto", "cbmc", "bounded"], default="auto", help="Search engine.")
    parser.add_argument("--values-per-param", type=int, default=18, help="Maximum generated values per parameter.")
    parser.add_argument("--max-candidates", type=int, default=5000, help="Maximum bounded candidate cases.")
    parser.add_argument("--max-timeouts", type=int, default=25, help="Stop bounded search after this many timed-out candidates.")
    parser.add_argument("--seed", type=int, default=1, help="Random seed for sampled bounded candidates.")
    parser.add_argument("--unwind", type=int, default=8, help="CBMC loop unwind bound.")
    parser.add_argument("--timeout", type=float, default=10.0, help="Timeout in seconds per generated program run.")
    parser.add_argument("--json", action="store_true", help="Print machine-readable JSON.")
    parser.add_argument("--keep", action="store_true", help="Keep generated harness files.")
    args = parser.parse_args(argv)

    original_source, _, original_function = parse_c_file(Path(args.original))
    mutant_source, _, mutant_function = parse_c_file(Path(args.mutant))
    del original_source, mutant_source

    parameters, return_type = compatible_signatures(original_function, mutant_function)
    clone_with_name(original_function, ORIGINAL_NAME)
    clone_with_name(mutant_function, MUTANT_NAME)
    rendered_functions = render_functions(original_function, mutant_function)

    domain_overrides = load_domain(args.domain, parameters) if args.domain else {}
    seed_cases = load_seed_cases(args.cases, parameters)
    generated_cases = generate_candidate_cases(
        parameters=parameters,
        existing_cases=seed_cases,
        domain_overrides=domain_overrides,
        values_per_param=max(1, args.values_per_param),
        max_candidates=max(1, args.max_candidates),
        seed=args.seed,
    )
    bounded_cases = unique_case_list(seed_cases + generated_cases)
    cbmc_domain = build_domain(parameters, domain_overrides, max(1, args.values_per_param))

    kept_dir: Path | None = None
    result: KillResult | None = None
    cbmc_hint: str | None = None
    bounded_timeout_hint: str | None = None

    if args.engine in {"auto", "cbmc"}:
        try:
            cbmc_case, kept_dir, _ = run_cbmc(
                rendered_functions=rendered_functions,
                return_type=return_type,
                parameters=parameters,
                domain=cbmc_domain,
                unwind=args.unwind,
                timeout=args.timeout,
                keep=args.keep,
            )
            if cbmc_case is not None:
                verification, bounded_kept, _, _ = bounded_search(
                    rendered_functions=rendered_functions,
                    return_type=return_type,
                    parameters=parameters,
                    cases=[cbmc_case],
                    timeout=args.timeout,
                    keep=False,
                    max_timeouts=1,
                )
                if verification is not None:
                    result = KillResult(
                        killed=True,
                        inputs=verification.inputs,
                        original_output=verification.original_output,
                        mutant_output=verification.mutant_output,
                        engine="cbmc",
                        hints=[],
                    )
                del bounded_kept
        except RuntimeError as exc:
            cbmc_hint = str(exc)
            if args.engine == "cbmc":
                raise SystemExit(cbmc_hint) from exc

    if result is None and args.engine in {"auto", "bounded"}:
        result, bounded_kept, timeout_count, stopped_for_timeouts = bounded_search(
            rendered_functions=rendered_functions,
            return_type=return_type,
            parameters=parameters,
            cases=bounded_cases,
            timeout=args.timeout,
            keep=args.keep and kept_dir is None,
            max_timeouts=max(1, args.max_timeouts),
        )
        if kept_dir is None:
            kept_dir = bounded_kept
        if stopped_for_timeouts:
            bounded_timeout_hint = (
                f"Bounded search stopped after {timeout_count} timed-out candidate(s); "
                "some mutants may not terminate for parts of the candidate domain."
            )

    if result is None:
        hints = [
            "No candidate produced a different return value.",
            "The mutant may be equivalent, the changed predicate may not affect the return value, or the search domain/unwind bound may be too small.",
            "Try --domain with targeted values, increase --values-per-param/--max-candidates, or increase --unwind for loop-heavy functions.",
        ]
        if cbmc_hint:
            hints.append(f"CBMC note: {cbmc_hint.splitlines()[0]}")
        if bounded_timeout_hint:
            hints.append(bounded_timeout_hint)
        result = KillResult(False, [], "", "", args.engine, hints)

    if args.json:
        print(json.dumps(result_to_json(result, parameters), indent=2))
    else:
        print_report(result, parameters, Path(args.original), Path(args.mutant), kept_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
