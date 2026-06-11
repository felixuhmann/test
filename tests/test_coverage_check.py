from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from test_support import (
    COVERAGE_CHECK_SCRIPT,
    load_coverage_check,
    require_gcc,
    run_cli,
    write_json,
    write_text,
)


class CoverageParsingAndUtilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.cov = load_coverage_check()

    def test_parse_c_file_strips_comments_and_preprocessor_lines(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "choice.c",
                """
                #include <stdbool.h>
                int choose(int a, int b) {
                    char slash = '/';
                    // the parser should not see this comment
                    if (a > 0 && b > 0) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )

            source, _, function = self.cov.parse_c_file(c_path)
            params = self.cov.function_parameters(function)

        self.assertIn("choose", source)
        self.assertEqual(self.cov.function_name(function), "choose")
        self.assertEqual([(param.name, param.type_name) for param in params], [("a", "int"), ("b", "int")])

    def test_load_cases_accepts_positional_objects_and_single_scalars(self) -> None:
        params = [self.cov.ParameterInfo("x", "int"), self.cov.ParameterInfo("flag", "bool")]
        with tempfile.TemporaryDirectory() as tmp:
            object_cases = write_json(
                Path(tmp) / "object_cases.json",
                {"cases": [{"flag": True, "x": 7}, [1, False]]},
            )
            scalar_cases = write_json(Path(tmp) / "scalar_cases.json", {"cases": [0, 1, 2]})

            self.assertEqual(self.cov.load_cases(object_cases, params), [[7, True], [1, False]])
            self.assertEqual(
                self.cov.load_cases(scalar_cases, [self.cov.ParameterInfo("x", "int")]),
                [[0], [1], [2]],
            )

    def test_load_cases_reports_shape_errors(self) -> None:
        params = [self.cov.ParameterInfo("x", "int"), self.cov.ParameterInfo("y", "int")]
        with tempfile.TemporaryDirectory() as tmp:
            cases = write_json(Path(tmp) / "bad.json", {"cases": [[1]]})

            with self.assertRaisesRegex(SystemExit, "takes 2 parameters"):
                self.cov.load_cases(cases, params)

    def test_value_to_c_literal_handles_raw_bool_char_and_numbers(self) -> None:
        self.assertEqual(self.cov.value_to_c_literal({"$c": "UINT_MAX"}, "unsigned int"), "UINT_MAX")
        self.assertEqual(self.cov.value_to_c_literal(True, "bool"), "true")
        self.assertEqual(self.cov.value_to_c_literal("false", "_Bool"), "false")
        self.assertEqual(self.cov.value_to_c_literal("\n", "char"), "'\\n'")
        self.assertEqual(self.cov.value_to_c_literal(3.5, "double"), "3.5")

    def test_analyzer_finds_statements_branches_decisions_and_conditions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "choice.c",
                """
                int choose(int a, int b) {
                    int result = 0;
                    if (a > 0 && b > 0) {
                        result = 1;
                    } else {
                        result = -1;
                    }
                    return result;
                }
                """,
            )
            _, _, function = self.cov.parse_c_file(c_path)
            analysis = self.cov.CoverageAnalyzer(line_offset=self.cov.PARSER_PREFIX_LINES)
            analysis.analyze_function(function)

        self.assertGreaterEqual(len(analysis.statements), 5)
        self.assertEqual(len(analysis.decisions), 1)
        self.assertEqual(len(analysis.branches), 2)
        self.assertEqual([condition.expression for condition in analysis.decisions[0].conditions], ["a > 0", "b > 0"])

    def test_runtime_output_parser_keeps_all_observations_and_overflow_flags(self) -> None:
        output = "\n".join(
            [
                "S 0 1",
                "S 1 0",
                "D 0 1 0",
                "C 0 0 1 0",
                "O 0 1 10",
                "O 0 0 00",
                "X 0",
            ]
        )

        runtime = self.cov.parse_runtime_output(output)

        self.assertEqual(runtime.statement_seen, {0: True, 1: False})
        self.assertEqual(runtime.decision_seen, {0: (True, False)})
        self.assertEqual(runtime.condition_seen[(0, 0)], (True, False))
        self.assertEqual(runtime.observations[0], [(1, "10"), (0, "00")])
        self.assertEqual(runtime.overflow_decisions, {0})

    def test_mcdc_computation_detects_independent_condition_pairs(self) -> None:
        decision = self.cov.DecisionInfo(
            id=0,
            line=1,
            expression="a && b",
            conditions=[
                self.cov.ConditionInfo(0, 1, "a"),
                self.cov.ConditionInfo(1, 1, "b"),
            ],
        )

        covered = self.cov.compute_mcdc(decision, [(0, "10"), (1, "11"), (0, "01")])

        self.assertEqual(covered, [True, True])

    def test_mcdc_treats_short_circuited_conditions_as_compatible(self) -> None:
        decision = self.cov.DecisionInfo(
            id=0,
            line=1,
            expression="a && b",
            conditions=[
                self.cov.ConditionInfo(0, 1, "a"),
                self.cov.ConditionInfo(1, 1, "b"),
            ],
        )

        # "0-" is a == 0 with b never evaluated; it pairs with "11" for a
        # because the skipped condition cannot have influenced the outcome.
        covered = self.cov.compute_mcdc(decision, [(0, "0-"), (1, "11"), (0, "10")])

        self.assertEqual(covered, [True, True])
        # Two unevaluated marks never demonstrate independence on their own.
        self.assertEqual(self.cov.compute_mcdc(decision, [(0, "0-"), (1, "1-")]), [True, False])

    def test_write_case_template_uses_parameter_aware_defaults(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "cases.json"
            params = [self.cov.ParameterInfo("x", "int"), self.cov.ParameterInfo("ok", "bool")]

            self.cov.write_case_template(out, params)
            data = json.loads(out.read_text(encoding="utf-8"))

        self.assertEqual(data["cases"], [[0, False], [1, True]])
        self.assertIn("_notes", data)


@unittest.skipUnless(require_gcc(), "gcc is required for dynamic coverage checker tests")
class CoverageCliIntegrationTests(unittest.TestCase):
    def test_json_report_is_fully_covered_for_mcdc_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "choice.c",
                """
                int choose(int a, int b) {
                    if (a > 0 && b > 0) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [[1, 1], [0, 1], [1, 0]]})

            result = run_cli([COVERAGE_CHECK_SCRIPT, c_path, cases, "--json"], timeout=20)

        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["function"], "choose")
        for criterion in ["statement", "branch", "decision", "condition", "mcdc"]:
            self.assertTrue(report["coverage"][criterion]["covered"], criterion)
            self.assertEqual(report["coverage"][criterion]["missing"], [])

    def test_json_report_lists_missing_false_paths_for_incomplete_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "choice.c",
                """
                int choose(int a, int b) {
                    if (a > 0 && b > 0) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [[1, 1]]})

            result = run_cli([COVERAGE_CHECK_SCRIPT, c_path, cases, "--json"], timeout=20)

        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertFalse(report["coverage"]["branch"]["covered"])
        self.assertFalse(report["coverage"]["decision"]["covered"])
        self.assertFalse(report["coverage"]["condition"]["covered"])
        self.assertFalse(report["coverage"]["mcdc"]["covered"])
        self.assertIn("false", report["coverage"]["decision"]["missing"][0]["missing"])

    def test_text_report_contains_covered_sections(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "abs.c",
                """
                int absish(int x) {
                    if (x < 0) {
                        return -x;
                    }
                    return x;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [-1, 0]})

            result = run_cli([COVERAGE_CHECK_SCRIPT, c_path, cases], timeout=20)

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Function: absish(int x)", result.stdout)
        self.assertIn("Statement coverage: covered", result.stdout)
        self.assertIn("Branch coverage: covered", result.stdout)

    def test_short_circuit_guard_is_preserved_by_instrumentation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "guard.c",
                """
                int h(int x) {
                    if (x != 0 && 100 / x > 2) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )
            # x == 0 must not evaluate the division: the instrumented program
            # has to keep C's short-circuit semantics instead of crashing.
            cases = write_json(tmp_path / "cases.json", {"cases": [0, 10, 100]})

            result = run_cli([COVERAGE_CHECK_SCRIPT, c_path, cases, "--json"], timeout=20)

        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        for criterion in ["statement", "branch", "decision", "condition", "mcdc"]:
            self.assertTrue(report["coverage"][criterion]["covered"], criterion)

    def test_init_cases_cli_writes_template_and_exits(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "one.c",
                """
                int one(int x) {
                    return x + 1;
                }
                """,
            )
            cases = tmp_path / "cases.json"

            result = run_cli([COVERAGE_CHECK_SCRIPT, c_path, cases, "--init-cases"], timeout=20)

            data = json.loads(cases.read_text(encoding="utf-8"))

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(data["cases"], [0, 1])
        self.assertIn("Wrote", result.stdout)


if __name__ == "__main__":
    unittest.main()
