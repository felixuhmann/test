from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from test_support import DATA_FLOW_SCRIPT, load_data_flow_check, require_gcc, run_cli, write_json, write_text


class DataFlowStaticAnalysisTests(unittest.TestCase):
    def setUp(self) -> None:
        self.df = load_data_flow_check()

    def _analyze_flow_function(self, tmp_path: Path):
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
        source, _, function = self.df.parse_c_file(c_path)
        parameters = self.df.function_parameters(function)
        analysis = self.df.DataFlowAnalyzer(function, parameters, self.df.PARSER_PREFIX_LINES)
        obligations = analysis.analyze()
        return source, function, parameters, analysis, obligations

    def test_variable_collector_tracks_parameters_and_locals(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            _, _, _, analysis, _ = self._analyze_flow_function(Path(tmp))

        variables = [(variable.name, variable.kind) for variable in analysis.variables]
        self.assertEqual(variables, [("x", "parameter"), ("y", "local")])

    def test_static_analysis_records_defs_c_uses_p_uses_and_decisions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            _, _, _, analysis, obligations = self._analyze_flow_function(Path(tmp))

        self.assertGreaterEqual(len(analysis.defs), 4)
        self.assertGreaterEqual(len(analysis.c_uses), 4)
        self.assertEqual(len(analysis.p_uses), 1)
        self.assertEqual(len(analysis.decisions), 1)
        self.assertTrue(obligations.c_uses)
        self.assertTrue(obligations.p_uses)

    def test_runtime_output_parser_records_case_indexes(self) -> None:
        runtime = self.df.parse_runtime_output(
            "\n".join(
                [
                    "C 0 1 7",
                    "C 2 3 8",
                    "P 0 4 1 9",
                    "P 2 5 0 10",
                ]
            )
        )

        self.assertEqual(runtime.c_uses, {(0, 1), (2, 3)})
        self.assertEqual(runtime.c_case[(0, 1)], 7)
        self.assertEqual(runtime.p_uses, {(0, 4, 1), (2, 5, 0)})
        self.assertEqual(runtime.p_case[(2, 5, 0)], 10)

    def test_missing_all_defs_marks_definitions_without_any_runtime_use(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            _, _, _, analysis, obligations = self._analyze_flow_function(Path(tmp))

        empty_runtime = self.df.RuntimeData(c_uses=set(), p_uses=set(), c_case={}, p_case={})
        missing = self.df.missing_all_defs_obligations(analysis, obligations, empty_runtime)

        self.assertEqual(missing, [definition.id for definition in analysis.defs])

    def test_json_report_has_complete_data_flow_sections(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            source, function, parameters, analysis, obligations = self._analyze_flow_function(Path(tmp))
            runtime = self.df.RuntimeData(
                c_uses=set(obligations.c_uses),
                p_uses=set(obligations.p_uses),
                c_case={key: 0 for key in obligations.c_uses},
                p_case={key: 0 for key in obligations.p_uses},
            )

            report = self.df.build_json_report(source, function, parameters, analysis=analysis, obligations=obligations, runtime=runtime, cases=[[0]])

        self.assertEqual(report["function"], "flow")
        self.assertTrue(report["coverage"]["all_c_uses"]["covered"])
        self.assertTrue(report["coverage"]["all_p_uses"]["covered"])
        self.assertTrue(report["coverage"]["all_du_pairs"]["covered"])

    def test_format_use_expression_keeps_context_when_use_is_embedded(self) -> None:
        self.assertEqual(self.df.format_use_expression("x", "x"), "x")
        self.assertEqual(self.df.format_use_expression("x", "x + 1"), "x in x + 1")


@unittest.skipUnless(require_gcc(), "gcc is required for dynamic data-flow checker tests")
class DataFlowCliIntegrationTests(unittest.TestCase):
    def test_json_report_is_fully_covered_for_true_and_false_paths(self) -> None:
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
            cases = write_json(tmp_path / "cases.json", {"cases": [0, -2]})

            result = run_cli([DATA_FLOW_SCRIPT, c_path, cases, "--json"], timeout=20)

        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        for criterion in [
            "all_defs",
            "all_c_uses",
            "all_p_uses",
            "all_du_pairs",
            "all_p_uses_some_c_uses",
        ]:
            self.assertTrue(report["coverage"][criterion]["covered"], criterion)

    def test_text_report_shows_missing_p_use_outcome_for_one_sided_suite(self) -> None:
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

            result = run_cli([DATA_FLOW_SCRIPT, c_path, cases], timeout=20)

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("All-p-uses: not covered", result.stdout)
        self.assertIn("outcome false", result.stdout)

    def test_json_report_keeps_source_line_excerpts_for_missing_obligations(self) -> None:
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

            result = run_cli([DATA_FLOW_SCRIPT, c_path, cases, "--json"], timeout=20)

        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        missing_p = report["coverage"]["all_p_uses"]["missing"]
        self.assertTrue(any("if (y > 0)" in item["use"]["source"] for item in missing_p))


if __name__ == "__main__":
    unittest.main()
