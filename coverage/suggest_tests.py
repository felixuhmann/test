#!/usr/bin/env python3
"""
Suggest additional test cases for one C function and one coverage criterion.

This is a bounded generator: it builds a finite candidate input domain, runs the
instrumented function over those candidates, and solves a minimum set-cover
problem over the observed coverage obligations.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pycparser import c_ast, c_generator

import data_flow_check
from coverage_check import (
    PARSER_PREFIX_LINES,
    CoverageAnalyzer,
    InstrumentingGenerator,
    compute_mcdc,
    function_name,
    function_parameters,
    load_cases,
    mcdc_bits_compatible,
    normalize_type_name,
    parse_c_file,
    value_to_c_literal,
)
from data_flow_check import DataFlowAnalyzer, StaticObligations


DATA_FLOW_CRITERIA = {
    "all-defs",
    "all-c-uses",
    "all-p-uses",
    "all-uses",
    "all-c-uses/some-p-uses",
    "all-p-uses/some-c-uses",
}
ALL_CRITERIA = sorted(DATA_FLOW_CRITERIA | {"mcdc"})


@dataclass(frozen=True)
class Candidate:
    id: int
    values: list[Any]
    output: str
    features: frozenset[tuple[Any, ...]]
    observations: tuple["MCDCObservation", ...] = ()


@dataclass(frozen=True)
class MCDCObservation:
    case_id: int | None
    decision_id: int
    result: int
    bits: str


@dataclass
class SuggestionResult:
    criterion: str
    already_covered: bool
    selected: list[Candidate]
    exact: bool
    covered: bool
    missing: list[str]
    hints: list[str]


def function_return_type(function: c_ast.FuncDef) -> str:
    generator = c_generator.CGenerator()
    return normalize_type_name(generator._generate_type(function.decl.type.type, emit_declname=False))


def is_void_type(type_name: str) -> bool:
    return normalize_type_name(type_name).lower() == "void"


def is_bool_type(type_name: str) -> bool:
    return normalize_type_name(type_name).lower() in {"bool", "_bool"}


def is_float_type(type_name: str) -> bool:
    normalized = normalize_type_name(type_name).lower()
    return normalized in {"float", "double", "long double"}


def is_unsigned_type(type_name: str) -> bool:
    normalized = normalize_type_name(type_name).lower()
    return "unsigned" in normalized or normalized in {"uint8_t", "uint16_t", "uint32_t", "uint64_t", "size_t"}


def is_signed_integer_type(type_name: str) -> bool:
    return not is_bool_type(type_name) and not is_float_type(type_name) and not is_unsigned_type(type_name)


def result_capture_lines(return_type: str, function: str, args: str, case_index: int) -> list[str]:
    if is_void_type(return_type):
        return [
            f"    {function}({args});",
            f"    printf(\"R {case_index} void\\n\");",
        ]

    if is_bool_type(return_type):
        return [
            f"    {return_type} __suggest_ret_{case_index} = {function}({args});",
            f"    printf(\"R {case_index} %s\\n\", __suggest_ret_{case_index} ? \"true\" : \"false\");",
        ]

    if is_float_type(return_type):
        return [
            f"    {return_type} __suggest_ret_{case_index} = {function}({args});",
            f"    printf(\"R {case_index} %.17Lg\\n\", (long double)__suggest_ret_{case_index});",
        ]

    if is_unsigned_type(return_type):
        return [
            f"    {return_type} __suggest_ret_{case_index} = {function}({args});",
            f"    printf(\"R {case_index} %llu\\n\", (unsigned long long)__suggest_ret_{case_index});",
        ]

    return [
        f"    {return_type} __suggest_ret_{case_index} = {function}({args});",
        f"    printf(\"R {case_index} %lld\\n\", (long long)__suggest_ret_{case_index});",
    ]


def case_to_c_args(case: list[Any], parameters: list[Any]) -> str:
    args = []
    for value, parameter in zip(case, parameters):
        literal = value_to_c_literal(value, parameter.type_name)
        args.append(f"(({parameter.type_name})({literal}))")
    return ", ".join(args)


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


def generate_indexed_main(start_case_call: str, case_bodies: list[list[str]], prelude_calls: list[str]) -> str:
    # One case per process invocation: a candidate input that crashes or does
    # not terminate is skipped instead of aborting the whole evaluation.
    lines = ["int main(int argc, char **argv) {"]
    for call in prelude_calls:
        lines.append(f"    {call}")
    lines.append("    int __suggest_case_index = argc > 1 ? atoi(argv[1]) : 0;")
    lines.append("    switch (__suggest_case_index) {")
    for index, body in enumerate(case_bodies):
        lines.append(f"    case {index}: {{")
        lines.append(f"        {start_case_call}({index});")
        lines.extend(f"    {line}" for line in body)
        lines.append("        break;")
        lines.append("    }")
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


def run_indexed_cases(binary: Path, case_count: int, timeout: float, max_timeouts: int) -> dict[int, str]:
    outputs: dict[int, str] = {}
    timeout_count = 0
    for index in range(case_count):
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
                print(
                    f"warning: stopped executing candidates after {timeout_count} timed-out case(s); "
                    "remaining candidates are treated as exercising nothing",
                    file=sys.stderr,
                )
                break
            continue
        if run_result.returncode != 0:
            continue
        outputs[index] = run_result.stdout
    return outputs


def generate_data_flow_runtime(var_count: int, p_use_count: int, p_use_decisions: list[int]) -> str:
    var_dim = max(1, var_count)
    p_dim = max(1, p_use_count)
    decision_table = data_flow_check.p_use_decision_table(p_use_decisions)
    return f"""\
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <float.h>

#define __DF_VAR_COUNT {var_count}
#define __DF_P_USE_COUNT {p_use_count}

static int __df_current_def[{var_dim}];
static unsigned char __df_p_touched[{p_dim}];
static int __df_p_touched_def[{p_dim}];
static const int __df_p_use_decision[{p_dim}] = {{{decision_table}}};
static int __df_current_case = -1;

static void __df_init_once(void) {{
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
    if (var_id < 0 || var_id >= __DF_VAR_COUNT) {{
        return;
    }}
    def_id = __df_current_def[var_id];
    if (def_id < 0) {{
        return;
    }}
    printf("C %d %d %d\\n", __df_current_case, def_id, use_id);
}}

static void __df_begin_pred(int decision_id) {{
    int i;
    for (i = 0; i < __DF_P_USE_COUNT; ++i) {{
        if (__df_p_use_decision[i] != decision_id) {{
            continue;
        }}
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
    if (def_id < 0) {{
        return;
    }}
    __df_p_touched[use_id] = 1;
    __df_p_touched_def[use_id] = def_id;
}}

static void __df_end_pred(int decision_id, int result) {{
    int i;
    int outcome = !!result;
    for (i = 0; i < __DF_P_USE_COUNT; ++i) {{
        int def_id;
        if (__df_p_use_decision[i] != decision_id) {{
            continue;
        }}
        if (!__df_p_touched[i]) {{
            continue;
        }}
        __df_p_touched[i] = 0;
        def_id = __df_p_touched_def[i];
        if (def_id < 0) {{
            continue;
        }}
        printf("P %d %d %d %d\\n", __df_current_case, def_id, i, outcome);
    }}
}}
"""


def generate_data_flow_harness(
    function: c_ast.FuncDef,
    analysis: DataFlowAnalyzer,
    parameters: list[Any],
    cases: list[list[Any]],
) -> str:
    runtime = generate_data_flow_runtime(
        len(analysis.variables),
        len(analysis.p_uses),
        data_flow_check.p_use_decisions(analysis),
    )
    instrumented_function = data_flow_check.DataFlowGenerator(analysis).visit(function)
    return_type = function_return_type(function)
    name = function_name(function)
    case_bodies = [
        result_capture_lines(return_type, name, case_to_c_args(case, parameters), index)
        for index, case in enumerate(cases)
    ]
    main = generate_indexed_main("__df_start_case", case_bodies, ["__df_init_once();"])
    return runtime + "\n" + instrumented_function + "\n" + main


def parse_data_flow_candidate_output(output: str) -> tuple[dict[int, set[tuple[Any, ...]]], dict[int, str]]:
    features: dict[int, set[tuple[Any, ...]]] = {}
    outputs: dict[int, str] = {}
    for raw_line in output.splitlines():
        parts = raw_line.split(maxsplit=2)
        if not parts:
            continue
        if parts[0] == "C":
            _, case_index, rest = raw_line.split(maxsplit=2)
            def_id, use_id = rest.split()
            features.setdefault(int(case_index), set()).add(("C", int(def_id), int(use_id)))
        elif parts[0] == "P":
            split = raw_line.split()
            case_index = int(split[1])
            features.setdefault(case_index, set()).add(("P", int(split[2]), int(split[3]), int(split[4])))
        elif parts[0] == "R":
            split = raw_line.split(maxsplit=2)
            outputs[int(split[1])] = split[2] if len(split) > 2 else ""
    return features, outputs


def generate_mcdc_runtime(decision_count: int, max_conditions: int) -> str:
    dec_dim = max(1, decision_count)
    cond_dim = max(1, max_conditions)
    return f"""\
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <float.h>

#define __COV_DECISIONS {decision_count}
#define __COV_MAX_CONDITIONS {cond_dim}
#define __COV_COND_UNEVALUATED 2

static int __suggest_current_case = -1;
static unsigned char __cov_pending_values[{dec_dim}][{cond_dim}];

static void __cov_stmt(int id) {{
    (void)id;
}}

static void __suggest_start_case(int case_index) {{
    __suggest_current_case = case_index;
}}

static void __cov_begin_decision(int id) {{
    int i;
    if (id < 0 || id >= __COV_DECISIONS) {{
        return;
    }}
    for (i = 0; i < __COV_MAX_CONDITIONS; ++i) {{
        __cov_pending_values[id][i] = __COV_COND_UNEVALUATED;
    }}
}}

static int __cov_cond(int id, int index, int value) {{
    int normalized = !!value;
    if (id >= 0 && id < __COV_DECISIONS && index >= 0 && index < __COV_MAX_CONDITIONS) {{
        __cov_pending_values[id][index] = (unsigned char)normalized;
    }}
    return normalized;
}}

static void __cov_end_decision(int id, int result) {{
    int i;
    if (id < 0 || id >= __COV_DECISIONS) {{
        return;
    }}
    printf("O %d %d %d ", __suggest_current_case, id, !!result);
    for (i = 0; i < __COV_MAX_CONDITIONS; ++i) {{
        unsigned char value = __cov_pending_values[id][i];
        putchar(value == __COV_COND_UNEVALUATED ? '-' : (value ? '1' : '0'));
    }}
    putchar('\\n');
}}
"""


def generate_mcdc_harness(
    function: c_ast.FuncDef,
    analysis: CoverageAnalyzer,
    parameters: list[Any],
    cases: list[list[Any]],
) -> str:
    max_conditions = max((len(decision.conditions) for decision in analysis.decisions), default=1)
    runtime = generate_mcdc_runtime(len(analysis.decisions), max_conditions)
    instrumented_function = InstrumentingGenerator(analysis).visit(function)
    return_type = function_return_type(function)
    name = function_name(function)
    case_bodies = [
        result_capture_lines(return_type, name, case_to_c_args(case, parameters), index)
        for index, case in enumerate(cases)
    ]
    main = generate_indexed_main("__suggest_start_case", case_bodies, [])
    return runtime + "\n" + instrumented_function + "\n" + main


def parse_mcdc_candidate_output(output: str) -> tuple[dict[int, list[MCDCObservation]], dict[int, str]]:
    observations: dict[int, list[MCDCObservation]] = {}
    outputs: dict[int, str] = {}
    for raw_line in output.splitlines():
        parts = raw_line.split(maxsplit=4)
        if not parts:
            continue
        if parts[0] == "O":
            case_index = int(parts[1])
            observations.setdefault(case_index, []).append(
                MCDCObservation(
                    case_id=case_index,
                    decision_id=int(parts[2]),
                    result=int(parts[3]),
                    bits=parts[4] if len(parts) > 4 else "",
                )
            )
        elif parts[0] == "R":
            split = raw_line.split(maxsplit=2)
            outputs[int(split[1])] = split[2] if len(split) > 2 else ""
    return observations, outputs


def load_domain(path: Path | None, parameters: list[Any]) -> dict[str, list[Any]]:
    if path is None:
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        if len(data) != len(parameters):
            raise SystemExit("Domain list length must match the number of parameters.")
        return {parameter.name: values for parameter, values in zip(parameters, data)}
    if isinstance(data, dict):
        return {str(name): values for name, values in data.items() if isinstance(values, list)}
    raise SystemExit("Domain must be a JSON object keyed by parameter name, or a list of value lists.")


def generate_candidate_cases(
    parameters: list[Any],
    existing_cases: list[list[Any]],
    domain_overrides: dict[str, list[Any]],
    values_per_param: int,
    max_candidates: int,
    seed: int,
) -> list[list[Any]]:
    domains = []
    for index, parameter in enumerate(parameters):
        if parameter.name in domain_overrides:
            values = domain_overrides[parameter.name]
        else:
            values = default_domain(parameter.type_name)
            values += existing_neighbor_values(existing_cases, index, parameter.type_name)
        domains.append(limit_domain(unique_values(values), values_per_param))

    if not domains:
        return [[]]

    total = math.prod(len(domain) for domain in domains)
    cases: list[list[Any]] = []
    seen: set[str] = set()

    def add(case: list[Any]) -> None:
        key = canonical_case(case)
        if key not in seen:
            seen.add(key)
            cases.append(case)

    if total <= max_candidates:
        for values in itertools.product(*domains):
            add(list(values))
        return cases

    base = [zero_value_for_type(parameter.type_name) for parameter in parameters]
    add(base)
    for index, domain in enumerate(domains):
        for value in domain:
            case = list(base)
            case[index] = value
            add(case)

    for left in range(len(domains)):
        for right in range(left + 1, len(domains)):
            for left_value in domains[left]:
                for right_value in domains[right]:
                    case = list(base)
                    case[left] = left_value
                    case[right] = right_value
                    add(case)
                    if len(cases) >= max_candidates:
                        return cases

    rng = random.Random(seed)
    while len(cases) < max_candidates:
        add([rng.choice(domain) for domain in domains])
        if len(seen) >= total:
            break

    return cases


def default_domain(type_name: str) -> list[Any]:
    normalized = normalize_type_name(type_name).lower()
    if normalized in {"bool", "_bool"}:
        return [False, True]
    if is_float_type(type_name):
        return [0.0, 1.0, -1.0, 2.0, -2.0, 0.5, -0.5, 4.0, -4.0, 8.0, -8.0]
    if is_unsigned_type(type_name):
        return [0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255]
    return [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -5, 6, -6, 7, -7, 8, -8, 15, -15, 16, -16]


def existing_neighbor_values(existing_cases: list[list[Any]], parameter_index: int, type_name: str) -> list[Any]:
    values: list[Any] = []
    for case in existing_cases:
        if parameter_index >= len(case):
            continue
        value = case[parameter_index]
        if isinstance(value, bool):
            values.extend([False, True])
        elif isinstance(value, int):
            if is_unsigned_type(type_name):
                values.extend([max(0, value - 1), value, value + 1])
            else:
                values.extend([value - 1, value, value + 1])
        elif isinstance(value, float):
            values.extend([value - 1.0, value, value + 1.0])
    return values


def zero_value_for_type(type_name: str) -> Any:
    if is_bool_type(type_name):
        return False
    if is_float_type(type_name):
        return 0.0
    return 0


def unique_values(values: list[Any]) -> list[Any]:
    result = []
    seen = set()
    for value in values:
        key = canonical_value(value)
        if key not in seen:
            seen.add(key)
            result.append(value)
    return result


def canonical_value(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def canonical_case(case: list[Any]) -> str:
    return json.dumps(case, sort_keys=True)


def limit_domain(values: list[Any], limit: int) -> list[Any]:
    if len(values) <= limit:
        return values
    keep = values[:limit]
    if 0 in values and 0 not in keep:
        keep[-1] = 0
    return unique_values(keep)


def split_current_and_candidates(
    existing_cases: list[list[Any]],
    generated_cases: list[list[Any]],
    mode: str,
) -> tuple[list[list[Any]], list[list[Any]]]:
    if mode == "replace":
        return [], unique_case_list(existing_cases + generated_cases)
    existing_keys = {canonical_case(case) for case in existing_cases}
    candidates = [case for case in generated_cases if canonical_case(case) not in existing_keys]
    return existing_cases, unique_case_list(candidates)


def unique_case_list(cases: list[list[Any]]) -> list[list[Any]]:
    result = []
    seen = set()
    for case in cases:
        key = canonical_case(case)
        if key not in seen:
            seen.add(key)
            result.append(case)
    return result


def evaluate_data_flow_candidates(
    function: c_ast.FuncDef,
    parameters: list[Any],
    current_cases: list[list[Any]],
    candidate_cases: list[list[Any]],
    timeout: float,
    keep: bool,
    max_timeouts: int,
) -> tuple[DataFlowAnalyzer, StaticObligations, set[tuple[Any, ...]], list[Candidate], Path | None]:
    analysis = DataFlowAnalyzer(function, parameters, PARSER_PREFIX_LINES)
    obligations = analysis.analyze()
    all_cases = current_cases + candidate_cases
    harness = generate_data_flow_harness(function, analysis, parameters, all_cases)

    if keep:
        build_dir = Path(".suggest_build_dataflow")
        if build_dir.exists():
            shutil.rmtree(build_dir)
        build_dir.mkdir(parents=True)
        binary = compile_source(harness, build_dir, "suggest_dataflow")
        outputs = run_indexed_cases(binary, len(all_cases), timeout, max_timeouts)
        kept_dir: Path | None = build_dir
    else:
        with tempfile.TemporaryDirectory(prefix="suggest_dataflow_") as tmp:
            binary = compile_source(harness, Path(tmp), "suggest_dataflow")
            outputs = run_indexed_cases(binary, len(all_cases), timeout, max_timeouts)
        kept_dir = None

    feature_by_case, output_by_case = parse_data_flow_candidate_output("\n".join(outputs.values()))
    current_features: set[tuple[Any, ...]] = set()
    for index in range(len(current_cases)):
        current_features.update(feature_by_case.get(index, set()))

    candidates = []
    offset = len(current_cases)
    for local_index, case in enumerate(candidate_cases):
        case_index = offset + local_index
        candidates.append(
            Candidate(
                id=local_index,
                values=case,
                output=output_by_case.get(case_index, ""),
                features=frozenset(feature_by_case.get(case_index, set())),
            )
        )
    return analysis, obligations, current_features, candidates, kept_dir


def evaluate_mcdc_candidates(
    function: c_ast.FuncDef,
    parameters: list[Any],
    current_cases: list[list[Any]],
    candidate_cases: list[list[Any]],
    timeout: float,
    keep: bool,
    max_timeouts: int,
) -> tuple[CoverageAnalyzer, list[MCDCObservation], list[Candidate], Path | None]:
    analysis = CoverageAnalyzer(line_offset=PARSER_PREFIX_LINES)
    analysis.analyze_function(function)
    all_cases = current_cases + candidate_cases
    harness = generate_mcdc_harness(function, analysis, parameters, all_cases)

    if keep:
        build_dir = Path(".suggest_build_mcdc")
        if build_dir.exists():
            shutil.rmtree(build_dir)
        build_dir.mkdir(parents=True)
        binary = compile_source(harness, build_dir, "suggest_mcdc")
        outputs = run_indexed_cases(binary, len(all_cases), timeout, max_timeouts)
        kept_dir: Path | None = build_dir
    else:
        with tempfile.TemporaryDirectory(prefix="suggest_mcdc_") as tmp:
            binary = compile_source(harness, Path(tmp), "suggest_mcdc")
            outputs = run_indexed_cases(binary, len(all_cases), timeout, max_timeouts)
        kept_dir = None

    observations_by_case, output_by_case = parse_mcdc_candidate_output("\n".join(outputs.values()))
    current_observations: list[MCDCObservation] = []
    for index in range(len(current_cases)):
        current_observations.extend(
            MCDCObservation(None, obs.decision_id, obs.result, obs.bits)
            for obs in observations_by_case.get(index, [])
        )

    candidates = []
    offset = len(current_cases)
    for local_index, case in enumerate(candidate_cases):
        case_index = offset + local_index
        observations = tuple(
            MCDCObservation(local_index, obs.decision_id, obs.result, obs.bits)
            for obs in observations_by_case.get(case_index, [])
        )
        candidates.append(
            Candidate(
                id=local_index,
                values=case,
                output=output_by_case.get(case_index, ""),
                features=frozenset(),
                observations=observations,
            )
        )
    return analysis, current_observations, candidates, kept_dir


def data_flow_objective(
    criterion: str,
    analysis: DataFlowAnalyzer,
    obligations: StaticObligations,
) -> tuple[set[tuple[Any, ...]], list[tuple[str, set[tuple[Any, ...]]]], list[str]]:
    required: set[tuple[Any, ...]] = set()
    groups: list[tuple[str, set[tuple[Any, ...]]]] = []
    impossible: list[str] = []

    c_by_def = {
        definition.id: {("C", definition.id, use_id) for use_id in obligations.c_uses_by_def.get(definition.id, set())}
        for definition in analysis.defs
    }
    p_by_def = {
        definition.id: {
            ("P", definition.id, use_id, outcome)
            for use_id, outcome in obligations.p_uses_by_def.get(definition.id, set())
        }
        for definition in analysis.defs
    }

    if criterion == "all-c-uses":
        return {("C", definition_id, use_id) for definition_id, use_id in obligations.c_uses}, [], []

    if criterion == "all-p-uses":
        return {("P", definition_id, use_id, outcome) for definition_id, use_id, outcome in obligations.p_uses}, [], []

    if criterion == "all-uses":
        return (
            {("C", definition_id, use_id) for definition_id, use_id in obligations.c_uses}
            | {("P", definition_id, use_id, outcome) for definition_id, use_id, outcome in obligations.p_uses}
        ), [], []

    for definition in analysis.defs:
        c_options = c_by_def.get(definition.id, set())
        p_options = p_by_def.get(definition.id, set())

        if criterion == "all-defs":
            options = c_options | p_options
            if options:
                groups.append((f"DEF:{definition.id}", options))
            else:
                impossible.append(describe_definition(analysis, definition.id))
        elif criterion == "all-p-uses/some-c-uses":
            if p_options:
                required.update(p_options)
            elif c_options:
                groups.append((f"SOME-C:{definition.id}", c_options))
            else:
                impossible.append(describe_definition(analysis, definition.id))
        elif criterion == "all-c-uses/some-p-uses":
            if c_options:
                required.update(c_options)
            elif p_options:
                groups.append((f"SOME-P:{definition.id}", p_options))
            else:
                impossible.append(describe_definition(analysis, definition.id))

    return required, groups, impossible


def solve_data_flow(
    criterion: str,
    analysis: DataFlowAnalyzer,
    obligations: StaticObligations,
    current_features: set[tuple[Any, ...]],
    candidates: list[Candidate],
    exact_target_limit: int,
) -> SuggestionResult:
    required, groups, impossible = data_flow_objective(criterion, analysis, obligations)
    target_names: list[tuple[Any, ...] | str] = []
    covered_now: set[tuple[Any, ...] | str] = set()

    for target in sorted(required):
        target_names.append(target)
        if target in current_features:
            covered_now.add(target)

    for group_name, options in groups:
        target_names.append(group_name)
        if current_features & options:
            covered_now.add(group_name)

    missing_targets = [target for target in target_names if target not in covered_now]
    if not missing_targets and not impossible:
        return SuggestionResult(criterion, True, [], True, True, [], [])

    target_to_bit = {target: index for index, target in enumerate(missing_targets)}
    full_mask = (1 << len(missing_targets)) - 1
    group_options = {group_name: options for group_name, options in groups}

    candidate_masks: list[tuple[Candidate, int]] = []
    union_mask = 0
    for candidate in candidates:
        mask = 0
        for target in missing_targets:
            if isinstance(target, tuple):
                if target in candidate.features:
                    mask |= 1 << target_to_bit[target]
            elif candidate.features & group_options[target]:
                mask |= 1 << target_to_bit[target]
        if mask:
            candidate_masks.append((candidate, mask))
            union_mask |= mask

    uncovered_by_domain = [
        target
        for target in missing_targets
        if not (union_mask & (1 << target_to_bit[target]))
    ]
    if impossible or uncovered_by_domain:
        missing = [describe_data_flow_target(analysis, target) for target in uncovered_by_domain]
        missing.extend(f"No statically reachable use for {item}" for item in impossible)
        return SuggestionResult(
            criterion,
            False,
            [],
            True,
            False,
            missing,
            generic_data_flow_hints(),
        )

    selected, exact = solve_set_cover(candidate_masks, full_mask, exact_target_limit)
    if selected is None:
        return SuggestionResult(
            criterion,
            False,
            [],
            False,
            False,
            [describe_data_flow_target(analysis, target) for target in missing_targets],
            ["Increase --exact-target-limit or reduce the target domain with --domain."],
        )

    return SuggestionResult(criterion, False, selected, exact, True, [], [])


def solve_set_cover(
    candidate_masks: list[tuple[Candidate, int]],
    full_mask: int,
    exact_target_limit: int,
) -> tuple[list[Candidate] | None, bool]:
    target_count = full_mask.bit_count()
    if target_count > exact_target_limit:
        selected = greedy_set_cover(candidate_masks, full_mask)
        return selected, False

    best: dict[int, tuple[int, ...]] = {0: ()}
    for index, (_, mask) in enumerate(candidate_masks):
        snapshot = list(best.items())
        for old_mask, old_selection in snapshot:
            new_mask = old_mask | mask
            new_selection = old_selection + (index,)
            if new_mask not in best or len(new_selection) < len(best[new_mask]):
                best[new_mask] = new_selection

    if full_mask not in best:
        return None, True
    return [candidate_masks[index][0] for index in best[full_mask]], True


def greedy_set_cover(candidate_masks: list[tuple[Candidate, int]], full_mask: int) -> list[Candidate] | None:
    remaining = full_mask
    selected: list[Candidate] = []
    available = list(candidate_masks)
    while remaining:
        best_index = -1
        best_gain = 0
        for index, (_, mask) in enumerate(available):
            gain = (mask & remaining).bit_count()
            if gain > best_gain:
                best_gain = gain
                best_index = index
        if best_index < 0:
            return None
        candidate, mask = available.pop(best_index)
        selected.append(candidate)
        remaining &= ~mask
    return selected


def solve_mcdc(
    analysis: CoverageAnalyzer,
    current_observations: list[MCDCObservation],
    candidates: list[Candidate],
    max_additions: int,
    max_search_nodes: int,
) -> SuggestionResult:
    targets = {
        (decision.id, condition.id)
        for decision in analysis.decisions
        for condition in decision.conditions
    }
    current_covered = mcdc_covered_targets(analysis, current_observations)
    if targets <= current_covered:
        return SuggestionResult("mcdc", True, [], True, True, [], [])

    selectors = build_mcdc_selectors(analysis, current_observations, candidates)
    missing_targets = targets - current_covered
    impossible = [target for target in sorted(missing_targets) if not selectors.get(target)]
    if impossible:
        return SuggestionResult(
            "mcdc",
            False,
            [],
            True,
            False,
            [describe_mcdc_target(analysis, target) for target in impossible],
            [
                "No generated candidate pair produced opposite decision outcomes with only this condition changing.",
                "That usually means the condition is logically coupled with another condition, or the generated input domain is too small.",
                "Try a custom --domain file if you believe the missing pair is feasible.",
            ],
        )

    selected = search_mcdc_selectors(selectors, missing_targets, max_additions, max_search_nodes)
    if selected is None:
        return SuggestionResult(
            "mcdc",
            False,
            [],
            True,
            False,
            [describe_mcdc_target(analysis, target) for target in sorted(missing_targets)],
            ["Increase --max-additions or --max-search-nodes."],
        )

    selected_candidates = [candidates[index] for index in sorted(selected)]
    return SuggestionResult("mcdc", False, selected_candidates, True, True, [], [])


def mcdc_covered_targets(analysis: CoverageAnalyzer, observations: list[MCDCObservation]) -> set[tuple[int, int]]:
    covered: set[tuple[int, int]] = set()
    by_decision: dict[int, list[tuple[int, str]]] = {}
    for observation in observations:
        by_decision.setdefault(observation.decision_id, []).append((observation.result, observation.bits))
    for decision in analysis.decisions:
        result = compute_mcdc(decision, by_decision.get(decision.id, []))
        for condition, is_covered in zip(decision.conditions, result):
            if is_covered:
                covered.add((decision.id, condition.id))
    return covered


def build_mcdc_selectors(
    analysis: CoverageAnalyzer,
    current_observations: list[MCDCObservation],
    candidates: list[Candidate],
) -> dict[tuple[int, int], list[frozenset[int]]]:
    all_observations = list(current_observations)
    for candidate in candidates:
        all_observations.extend(candidate.observations)

    selectors: dict[tuple[int, int], set[frozenset[int]]] = defaultdict(set)
    for decision in analysis.decisions:
        states: dict[tuple[int, str], set[int | None]] = defaultdict(set)
        for observation in all_observations:
            if observation.decision_id == decision.id:
                states[(observation.result, observation.bits)].add(observation.case_id)

        state_items = list(states.items())
        for left_index, ((left_result, left_bits), left_sources) in enumerate(state_items):
            left = MCDCObservation(None, decision.id, left_result, left_bits)
            for (right_result, right_bits), right_sources in state_items[left_index + 1 :]:
                right = MCDCObservation(None, decision.id, right_result, right_bits)
                for condition in decision.conditions:
                    if not mcdc_pair_covers(condition.id, len(decision.conditions), left, right):
                        continue
                    selectors[(decision.id, condition.id)].update(
                        source_selectors(left_sources, right_sources)
                    )

    return {
        target: sorted(remove_selector_supersets(options), key=lambda option: (len(option), sorted(option)))
        for target, options in selectors.items()
    }


def source_selectors(left_sources: set[int | None], right_sources: set[int | None]) -> set[frozenset[int]]:
    selectors: set[frozenset[int]] = set()
    if None in left_sources and None in right_sources:
        selectors.add(frozenset())
        return selectors

    left_candidates = {source for source in left_sources if source is not None}
    right_candidates = {source for source in right_sources if source is not None}

    if None in left_sources:
        selectors.update(frozenset({source}) for source in right_candidates)
        return selectors
    if None in right_sources:
        selectors.update(frozenset({source}) for source in left_candidates)
        return selectors

    for left in left_candidates:
        for right in right_candidates:
            selectors.add(frozenset({left, right}))
    return selectors


def mcdc_pair_covers(condition_id: int, condition_count: int, left: MCDCObservation, right: MCDCObservation) -> bool:
    if left.result == right.result:
        return False
    if len(left.bits) < condition_count or len(right.bits) < condition_count:
        return False
    left_bit = left.bits[condition_id]
    right_bit = right.bits[condition_id]
    if left_bit not in "01" or right_bit not in "01" or left_bit == right_bit:
        return False
    return all(
        mcdc_bits_compatible(left.bits[index], right.bits[index])
        for index in range(condition_count)
        if index != condition_id
    )


def remove_selector_supersets(options: set[frozenset[int]]) -> set[frozenset[int]]:
    minimal = set(options)
    for left in options:
        for right in options:
            if left != right and right < left:
                minimal.discard(left)
                break
    return minimal


def search_mcdc_selectors(
    selectors: dict[tuple[int, int], list[frozenset[int]]],
    targets: set[tuple[int, int]],
    max_additions: int,
    max_search_nodes: int,
) -> set[int] | None:
    targets = set(targets)
    best: set[int] | None = None
    visited_nodes = 0

    def covered(selected: set[int], target: tuple[int, int]) -> bool:
        return any(option <= selected for option in selectors[target])

    def recurse(selected: set[int]) -> None:
        nonlocal best, visited_nodes
        visited_nodes += 1
        if visited_nodes > max_search_nodes:
            return
        if best is not None and len(selected) >= len(best):
            return
        if len(selected) > max_additions:
            return
        uncovered = [target for target in targets if not covered(selected, target)]
        if not uncovered:
            best = set(selected)
            return
        target = min(
            uncovered,
            key=lambda item: min(len(option - selected) for option in selectors[item]),
        )
        choices = sorted(
            selectors[target],
            key=lambda option: (len(option - selected), len(option), sorted(option)),
        )
        for option in choices:
            new_selected = selected | set(option)
            if len(new_selected) <= max_additions:
                recurse(new_selected)

    for limit in range(0, max_additions + 1):
        previous_best = best
        max_additions_for_limit = limit

        def recurse_limited(selected: set[int]) -> None:
            nonlocal best, visited_nodes
            visited_nodes += 1
            if visited_nodes > max_search_nodes:
                return
            if len(selected) > max_additions_for_limit:
                return
            uncovered = [target for target in targets if not covered(selected, target)]
            if not uncovered:
                best = set(selected)
                return
            target = min(
                uncovered,
                key=lambda item: min(len(option - selected) for option in selectors[item]),
            )
            for option in sorted(selectors[target], key=lambda option: (len(option - selected), len(option), sorted(option))):
                new_selected = selected | set(option)
                if len(new_selected) <= max_additions_for_limit:
                    recurse_limited(new_selected)
                    if best is not previous_best and best is not None and len(best) <= max_additions_for_limit:
                        return

        recurse_limited(set())
        if best is not previous_best and best is not None:
            return best
        if visited_nodes > max_search_nodes:
            return None

    recurse(set())
    return best


def describe_definition(analysis: DataFlowAnalyzer, definition_id: int) -> str:
    definition = analysis.defs[definition_id]
    return f"`{definition.var_name}` definition at line {definition.line} ({definition.description})"


def describe_data_flow_target(analysis: DataFlowAnalyzer, target: tuple[Any, ...] | str) -> str:
    if isinstance(target, str):
        prefix, definition_id_text = target.split(":", maxsplit=1)
        definition = analysis.defs[int(definition_id_text)]
        if prefix == "SOME-C":
            return f"some c-use from {describe_definition(analysis, definition.id)}"
        if prefix == "SOME-P":
            return f"some p-use from {describe_definition(analysis, definition.id)}"
        return f"some use from {describe_definition(analysis, definition.id)}"

    if target[0] == "C":
        _, definition_id, use_id = target
        definition = analysis.defs[definition_id]
        use = analysis.c_uses[use_id]
        return (
            f"`{definition.var_name}` def line {definition.line} -> "
            f"c-use line {use.line} `{use.expression}`"
        )

    _, definition_id, use_id, outcome = target
    definition = analysis.defs[definition_id]
    use = analysis.p_uses[use_id]
    return (
        f"`{definition.var_name}` def line {definition.line} -> "
        f"p-use line {use.line} `{use.expression}` outcome {'true' if outcome else 'false'}"
    )


def describe_mcdc_target(analysis: CoverageAnalyzer, target: tuple[int, int]) -> str:
    decision_id, condition_id = target
    decision = analysis.decisions[decision_id]
    condition = decision.conditions[condition_id]
    return (
        f"decision line {decision.line} `{decision.expression}`, "
        f"condition `{condition.expression}`"
    )


def generic_data_flow_hints() -> list[str]:
    return [
        "No generated candidate exercised this obligation.",
        "The def-use path may be semantically infeasible, or the generated input domain may be too small.",
        "Try a custom --domain file with values that drive the missing branch or loop path.",
    ]


def print_text_report(
    result: SuggestionResult,
    parameters: list[Any],
    mode: str,
    generated_count: int,
    kept_dir: Path | None,
) -> None:
    print(f"Criterion: {result.criterion}")
    print(f"Mode: {mode}")
    print(f"Generated candidate cases: {generated_count}")
    if result.already_covered:
        print("Status: already covered by the current cases.")
    elif result.covered:
        label = "additional" if mode == "augment" else "selected"
        exact_text = "exact minimum" if result.exact else "greedy approximation"
        print(f"Status: covered with {len(result.selected)} {label} case(s) ({exact_text} over generated candidates).")
        print("Suggested cases:")
        for index, candidate in enumerate(result.selected, start=1):
            values = {
                parameter.name: value
                for parameter, value in zip(parameters, candidate.values)
            }
            print(f"  {index}. inputs: {json.dumps(values, sort_keys=True)} -> output: {candidate.output}")
        print("As cases.json entries:")
        for candidate in result.selected:
            print(f"  {json.dumps(candidate.values)}")
    else:
        print("Status: not covered within the generated candidate domain.")
        if result.missing:
            print("Still missing:")
            for item in result.missing[:20]:
                print(f"  - {item}")
            if len(result.missing) > 20:
                print(f"  ... {len(result.missing) - 20} more")
        if result.hints:
            print("Hints:")
            for hint in result.hints:
                print(f"  - {hint}")
    if kept_dir is not None:
        print(f"Kept generated files in {kept_dir}")


def result_to_json(result: SuggestionResult, parameters: list[Any], mode: str, generated_count: int) -> dict[str, Any]:
    return {
        "criterion": result.criterion,
        "mode": mode,
        "generated_candidate_count": generated_count,
        "already_covered": result.already_covered,
        "covered": result.covered,
        "exact": result.exact,
        "suggested_cases": [
            {
                "inputs": {
                    parameter.name: value
                    for parameter, value in zip(parameters, candidate.values)
                },
                "case": candidate.values,
                "output": candidate.output,
            }
            for candidate in result.selected
        ],
        "missing": result.missing,
        "hints": result.hints,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Suggest minimal bounded test cases for a coverage criterion.")
    parser.add_argument("source", nargs="?", default="input.c", help="C file containing exactly one function. Default: input.c")
    parser.add_argument("cases", nargs="?", default="cases.json", help="JSON file with existing test cases. Default: cases.json")
    parser.add_argument(
        "--criterion",
        choices=ALL_CRITERIA,
        required=True,
        help="Coverage criterion to satisfy.",
    )
    parser.add_argument(
        "--mode",
        choices=["augment", "replace"],
        default="augment",
        help="augment suggests additional cases; replace finds a small suite from the generated domain.",
    )
    parser.add_argument("--domain", type=Path, help="Optional JSON domain keyed by parameter name, e.g. {\"a\":[0,1,2]}.")
    parser.add_argument("--values-per-param", type=int, default=18, help="Maximum generated values per parameter.")
    parser.add_argument("--max-candidates", type=int, default=5000, help="Maximum generated candidate input cases.")
    parser.add_argument("--max-additions", type=int, default=8, help="Maximum cases to add for MC/DC pair search.")
    parser.add_argument("--max-search-nodes", type=int, default=250000, help="Maximum MC/DC recursive search nodes.")
    parser.add_argument("--exact-target-limit", type=int, default=32, help="Use exact set cover up to this many missing data-flow targets.")
    parser.add_argument("--seed", type=int, default=1, help="Random seed used when candidate sampling is needed.")
    parser.add_argument("--timeout", type=float, default=10.0, help="Timeout in seconds per executed candidate case.")
    parser.add_argument("--max-timeouts", type=int, default=25, help="Stop executing candidates after this many timed-out cases.")
    parser.add_argument("--json", action="store_true", help="Print machine-readable JSON.")
    parser.add_argument("--keep", action="store_true", help="Keep the generated instrumented harness.")
    args = parser.parse_args(argv)

    source, _, function = parse_c_file(Path(args.source))
    parameters = function_parameters(function)
    existing_cases = load_cases(Path(args.cases), parameters)
    domain = load_domain(args.domain, parameters)
    generated_cases = generate_candidate_cases(
        parameters=parameters,
        existing_cases=existing_cases,
        domain_overrides=domain,
        values_per_param=max(1, args.values_per_param),
        max_candidates=max(1, args.max_candidates),
        seed=args.seed,
    )
    current_cases, candidate_cases = split_current_and_candidates(existing_cases, generated_cases, args.mode)

    if args.criterion in DATA_FLOW_CRITERIA:
        analysis, obligations, current_features, candidates, kept_dir = evaluate_data_flow_candidates(
            function=function,
            parameters=parameters,
            current_cases=current_cases,
            candidate_cases=candidate_cases,
            timeout=args.timeout,
            keep=args.keep,
            max_timeouts=max(1, args.max_timeouts),
        )
        result = solve_data_flow(
            criterion=args.criterion,
            analysis=analysis,
            obligations=obligations,
            current_features=current_features,
            candidates=candidates,
            exact_target_limit=args.exact_target_limit,
        )
    else:
        analysis, current_observations, candidates, kept_dir = evaluate_mcdc_candidates(
            function=function,
            parameters=parameters,
            current_cases=current_cases,
            candidate_cases=candidate_cases,
            timeout=args.timeout,
            keep=args.keep,
            max_timeouts=max(1, args.max_timeouts),
        )
        result = solve_mcdc(
            analysis=analysis,
            current_observations=current_observations,
            candidates=candidates,
            max_additions=args.max_additions,
            max_search_nodes=args.max_search_nodes,
        )

    if args.json:
        print(json.dumps(result_to_json(result, parameters, args.mode, len(candidate_cases)), indent=2))
    else:
        print_text_report(result, parameters, args.mode, len(candidate_cases), kept_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
