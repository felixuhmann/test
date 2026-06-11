from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from test_support import (
    SUGGEST_TESTS_SCRIPT,
    load_coverage_check,
    load_data_flow_check,
    load_suggest_tests,
    require_gcc,
    run_cli,
    write_json,
    write_text,
)


class SuggestionUtilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.suggest = load_suggest_tests()
        self.cov = load_coverage_check()

    def test_all_uses_is_exposed_as_a_cli_criterion(self) -> None:
        self.assertIn("all-uses", self.suggest.DATA_FLOW_CRITERIA)
        self.assertIn("all-uses", self.suggest.ALL_CRITERIA)

    def test_decision_and_condition_are_exposed_as_cli_criteria(self) -> None:
        self.assertIn("decision", self.suggest.CONTROL_FLOW_CRITERIA)
        self.assertIn("condition", self.suggest.CONTROL_FLOW_CRITERIA)
        self.assertIn("condition/decision", self.suggest.CONTROL_FLOW_CRITERIA)
        self.assertIn("decision", self.suggest.ALL_CRITERIA)
        self.assertIn("condition", self.suggest.ALL_CRITERIA)
        self.assertIn("condition/decision", self.suggest.ALL_CRITERIA)

    def test_default_domains_cover_common_primitive_values(self) -> None:
        self.assertEqual(self.suggest.default_domain("bool"), [False, True])
        self.assertEqual(self.suggest.default_domain("unsigned int")[:5], [0, 1, 2, 3, 4])
        signed = self.suggest.default_domain("int")
        self.assertIn(-1, signed)
        self.assertIn(16, signed)

    def test_generate_candidate_cases_uses_overrides_neighbors_and_deduplication(self) -> None:
        params = [self.cov.ParameterInfo("x", "int"), self.cov.ParameterInfo("flag", "bool")]

        cases = self.suggest.generate_candidate_cases(
            parameters=params,
            existing_cases=[[3, True]],
            domain_overrides={"x": [3, 4, 4]},
            values_per_param=3,
            max_candidates=20,
            seed=123,
        )

        self.assertIn([3, False], cases)
        self.assertIn([4, True], cases)
        self.assertEqual(len(cases), len({self.suggest.canonical_case(case) for case in cases}))

    def test_split_current_and_candidates_supports_augment_and_replace_modes(self) -> None:
        existing = [[0], [1]]
        generated = [[1], [2]]

        current, candidates = self.suggest.split_current_and_candidates(existing, generated, "augment")
        self.assertEqual(current, existing)
        self.assertEqual(candidates, [[2]])

        current, candidates = self.suggest.split_current_and_candidates(existing, generated, "replace")
        self.assertEqual(current, [])
        self.assertEqual(candidates, [[0], [1], [2]])

    def test_exact_set_cover_finds_minimum_number_of_candidates(self) -> None:
        candidates = [
            (self.suggest.Candidate(0, [0], "0", frozenset({("A",)})), 0b001),
            (self.suggest.Candidate(1, [1], "1", frozenset({("B",), ("C",)})), 0b110),
            (self.suggest.Candidate(2, [2], "2", frozenset({("A",), ("B",), ("C",)})), 0b111),
        ]

        selected, exact = self.suggest.solve_set_cover(candidates, full_mask=0b111, exact_target_limit=4)

        self.assertTrue(exact)
        self.assertEqual([candidate.id for candidate in selected], [2])

    def test_greedy_set_cover_returns_none_when_targets_are_unreachable(self) -> None:
        candidates = [(self.suggest.Candidate(0, [0], "0", frozenset()), 0b001)]

        selected = self.suggest.greedy_set_cover(candidates, full_mask=0b011)

        self.assertIsNone(selected)

    def test_mcdc_pair_and_source_selector_helpers(self) -> None:
        left = self.suggest.MCDCObservation(case_id=0, decision_id=0, result=0, bits="10")
        right = self.suggest.MCDCObservation(case_id=1, decision_id=0, result=1, bits="11")
        short_circuited = self.suggest.MCDCObservation(case_id=2, decision_id=0, result=0, bits="0-")

        self.assertTrue(self.suggest.mcdc_pair_covers(1, 2, left, right))
        self.assertFalse(self.suggest.mcdc_pair_covers(0, 2, left, right))
        self.assertTrue(self.suggest.mcdc_pair_covers(0, 2, short_circuited, right))
        self.assertFalse(self.suggest.mcdc_pair_covers(1, 2, short_circuited, right))
        self.assertEqual(
            self.suggest.source_selectors({None, 0}, {1}),
            {frozenset({1})},
        )
        self.assertEqual(
            self.suggest.remove_selector_supersets({frozenset({1}), frozenset({1, 2})}),
            {frozenset({1})},
        )

    def test_result_to_json_serializes_selected_cases_by_parameter_name(self) -> None:
        params = [self.cov.ParameterInfo("x", "int")]
        result = self.suggest.SuggestionResult(
            criterion="all-defs",
            already_covered=False,
            selected=[self.suggest.Candidate(0, [3], "4", frozenset({("C", 0, 0)}))],
            exact=True,
            covered=True,
            missing=[],
            hints=[],
        )

        payload = self.suggest.result_to_json(result, params, mode="augment", generated_count=5)

        self.assertEqual(payload["suggested_cases"][0]["inputs"], {"x": 3})
        self.assertEqual(payload["suggested_cases"][0]["output"], "4")


class SuggestionDataFlowObjectiveTests(unittest.TestCase):
    def setUp(self) -> None:
        self.suggest = load_suggest_tests()
        self.df = load_data_flow_check()

    def test_all_uses_objective_is_union_of_c_and_p_use_obligations(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "flow.c",
                """
                int flow(int x) {
                    int y = x + 1;
                    if (y > 0) {
                        y = y + 1;
                    }
                    return y;
                }
                """,
            )
            _, _, function = self.df.parse_c_file(c_path)
            parameters = self.df.function_parameters(function)
            analysis = self.df.DataFlowAnalyzer(function, parameters, self.df.PARSER_PREFIX_LINES)
            obligations = analysis.analyze()

            required, groups, impossible = self.suggest.data_flow_objective("all-uses", analysis, obligations)

        expected = {
            ("C", definition_id, use_id)
            for definition_id, use_id in obligations.c_uses
        } | {
            ("P", definition_id, use_id, outcome)
            for definition_id, use_id, outcome in obligations.p_uses
        }
        self.assertEqual(required, expected)
        self.assertEqual(groups, [])
        self.assertEqual(impossible, [])


@unittest.skipUnless(require_gcc(), "gcc is required for suggestion CLI integration tests")
class SuggestionCliIntegrationTests(unittest.TestCase):
    def test_decision_json_suggests_cases_that_complete_a_partial_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "sign.c",
                """
                int sign(int x) {
                    if (x > 0) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [1]})

            result = run_cli(
                [
                    SUGGEST_TESTS_SCRIPT,
                    c_path,
                    cases,
                    "--criterion",
                    "decision",
                    "--json",
                    "--values-per-param",
                    "4",
                    "--max-candidates",
                    "20",
                ],
                timeout=25,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["criterion"], "decision")
        self.assertTrue(payload["covered"])
        self.assertTrue(any(case["inputs"]["x"] <= 0 for case in payload["suggested_cases"]))

    def test_condition_json_suggests_cases_that_complete_a_partial_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "both.c",
                """
                int both(int a, int b) {
                    if (a > 0 && b > 0) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [[1, 1]]})

            result = run_cli(
                [
                    SUGGEST_TESTS_SCRIPT,
                    c_path,
                    cases,
                    "--criterion",
                    "condition",
                    "--json",
                    "--values-per-param",
                    "4",
                    "--max-candidates",
                    "30",
                ],
                timeout=25,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["criterion"], "condition")
        self.assertTrue(payload["covered"])
        self.assertTrue(any(case["inputs"]["a"] <= 0 for case in payload["suggested_cases"]))
        self.assertTrue(any(case["inputs"]["a"] > 0 and case["inputs"]["b"] <= 0 for case in payload["suggested_cases"]))

    def test_condition_decision_json_suggests_cases_that_complete_a_partial_suite(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "both.c",
                """
                int both(int a, int b) {
                    if (a > 0 && b > 0) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [[1, 1]]})

            result = run_cli(
                [
                    SUGGEST_TESTS_SCRIPT,
                    c_path,
                    cases,
                    "--criterion",
                    "condition/decision",
                    "--json",
                    "--values-per-param",
                    "4",
                    "--max-candidates",
                    "30",
                ],
                timeout=25,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["criterion"], "condition/decision")
        self.assertTrue(payload["covered"])
        self.assertTrue(any(case["inputs"]["a"] <= 0 for case in payload["suggested_cases"]))
        self.assertTrue(any(case["inputs"]["a"] > 0 and case["inputs"]["b"] <= 0 for case in payload["suggested_cases"]))

    def test_mcdc_json_suggests_cases_that_complete_a_partial_suite(self) -> None:
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

            result = run_cli(
                [
                    SUGGEST_TESTS_SCRIPT,
                    c_path,
                    cases,
                    "--criterion",
                    "mcdc",
                    "--json",
                    "--values-per-param",
                    "4",
                    "--max-candidates",
                    "20",
                    "--max-additions",
                    "3",
                ],
                timeout=25,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["criterion"], "mcdc")
        self.assertTrue(payload["covered"])
        self.assertGreaterEqual(len(payload["suggested_cases"]), 1)

    def test_crashing_candidates_are_skipped_not_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "div.c",
                """
                int d(int x) {
                    if (100 / x > 5) {
                        return 1;
                    }
                    return 0;
                }
                """,
            )
            # The generated domain contains x == 0, which crashes with SIGFPE;
            # that candidate must be dropped instead of aborting the run.
            cases = write_json(tmp_path / "cases.json", {"cases": [10]})

            result = run_cli(
                [
                    SUGGEST_TESTS_SCRIPT,
                    c_path,
                    cases,
                    "--criterion",
                    "mcdc",
                    "--json",
                    "--values-per-param",
                    "6",
                    "--max-candidates",
                    "20",
                ],
                timeout=30,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertTrue(payload["covered"])
        self.assertTrue(all(case["inputs"]["x"] != 0 for case in payload["suggested_cases"]))

    def test_nonterminating_candidates_are_skipped_not_fatal(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "loop.c",
                """
                int sumto(int n) {
                    int s = 0;
                    int i = 0;
                    while (i != n) {
                        s = s + i;
                        i = i + 1;
                    }
                    return s;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [3]})
            # n == -1 never terminates; it must time out individually while
            # the remaining candidates still produce a suggestion.
            domain = write_json(tmp_path / "domain.json", {"n": [-1, 0, 1, 2, 3, 4]})

            result = run_cli(
                [
                    SUGGEST_TESTS_SCRIPT,
                    c_path,
                    cases,
                    "--criterion",
                    "all-p-uses",
                    "--json",
                    "--domain",
                    domain,
                    "--timeout",
                    "1",
                ],
                timeout=40,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertTrue(payload["covered"])
        self.assertTrue(all(case["inputs"]["n"] != -1 for case in payload["suggested_cases"]))

    def test_all_uses_json_accepts_documented_criterion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "flow.c",
                """
                int flow(int x) {
                    int y = x + 1;
                    if (y > 0) {
                        y = y + 1;
                    } else {
                        y = y - 1;
                    }
                    return y;
                }
                """,
            )
            cases = write_json(tmp_path / "cases.json", {"cases": [0]})

            result = run_cli(
                [
                    SUGGEST_TESTS_SCRIPT,
                    c_path,
                    cases,
                    "--criterion",
                    "all-uses",
                    "--json",
                    "--values-per-param",
                    "5",
                    "--max-candidates",
                    "20",
                ],
                timeout=25,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["criterion"], "all-uses")
        self.assertTrue(payload["covered"])


if __name__ == "__main__":
    unittest.main()
