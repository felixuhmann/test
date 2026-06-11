from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from test_support import INVARIANT_SCRIPT, load_invariants, require_z3, run_cli, write_text


class InvariantFormulaParserTests(unittest.TestCase):
    def setUp(self) -> None:
        self.inv = load_invariants()

    def test_tokenizer_ignores_comments_and_tracks_keywords(self) -> None:
        tokens = self.inv.tokenize(
            """
            # worksheet comment
            pre { n >= 0 } // line comment
            candidate { i <= n && true }
            """
        )

        kinds = [token.kind for token in tokens]
        self.assertIn("pre", kinds)
        self.assertIn("candidate", kinds)
        self.assertIn("&&", kinds)
        self.assertEqual(kinds[-1], "eof")

    def test_directive_formula_file_supports_pre_reachable_and_multiple_candidates(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            formula_path = write_text(
                Path(tmp) / "invariant.txt",
                """
                pre { n >= 0 };
                reachable { i >= 0 };
                candidate { i <= n };
                invariant { i >= 0 };
                """,
            )

            parsed = self.inv.parse_formula_file(formula_path)

        self.assertEqual(parsed.pre.to_source(), "(n >= 0)")
        self.assertEqual(parsed.reachable.to_source(), "(i >= 0)")
        self.assertEqual([candidate.to_source() for candidate in parsed.candidates], ["(i <= n)", "(i >= 0)"])

    def test_plain_formula_file_without_directives_is_a_single_candidate(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            formula_path = write_text(Path(tmp) / "one.txt", "{ i == 0 || i > 0 }")

            parsed = self.inv.parse_formula_file(formula_path)

        self.assertEqual(parsed.pre, self.inv.BoolLit(True))
        self.assertEqual(len(parsed.candidates), 1)
        self.assertEqual(parsed.candidates[0].to_smt(), "(or (= i 0) (> i 0))")

    def test_formula_file_rejects_unknown_directive_text(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            formula_path = write_text(Path(tmp) / "bad.txt", "pre { n >= 0 } nonsense")

            with self.assertRaisesRegex(self.inv.InvariantError, "expected 'pre'"):
                self.inv.parse_formula_file(formula_path)


class InvariantCParserAndSymbolicTests(unittest.TestCase):
    def setUp(self) -> None:
        self.inv = load_invariants()

    def test_strip_comments_and_preprocessor_preserves_string_literals(self) -> None:
        source = '#include <stdio.h>\nchar *s = "not // a comment";\nint x; // real comment\n'

        sanitized = self.inv.strip_comments_and_preprocessor(source)

        self.assertNotIn("#include", sanitized)
        self.assertIn('"not // a comment"', sanitized)
        self.assertNotIn("real comment", sanitized)

    def test_parse_c_problem_collects_types_initialization_guard_and_body(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(unsigned int n, _Bool enabled) {
                    int i = 0;
                    if (enabled) {
                        i += 1;
                    }
                    while (i < n) {
                        i = i + 1;
                    }
                }
                """,
            )

            problem = self.inv.parse_c_problem(c_path)

        self.assertEqual(problem.function_name, "f")
        self.assertEqual(problem.types["n"], "Nat")
        self.assertEqual(problem.types["enabled"], "Bool")
        self.assertEqual(problem.types["i"], "Int")
        self.assertEqual(problem.guard.to_source(), "(i < n)")
        self.assertGreaterEqual(len(problem.init), 2)
        self.assertEqual(len(problem.body), 1)

    def test_parse_c_problem_rejects_nested_while(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "nested.c",
                """
                void f(int n) {
                    while (n > 0) {
                        while (n > 1) {
                            n = n - 1;
                        }
                    }
                }
                """,
            )

            with self.assertRaisesRegex(self.inv.InvariantError, "nested while"):
                self.inv.parse_c_problem(c_path)

    def test_symbolic_execute_substitutes_assignments_and_merges_if_branches(self) -> None:
        stmts = [
            self.inv.Assign(1, "x", self.inv.IntLit(0)),
            self.inv.If(
                2,
                self.inv.Var("flag"),
                [self.inv.Assign(3, "x", self.inv.Binary("+", self.inv.Var("x"), self.inv.IntLit(1)))],
                [self.inv.Assign(5, "x", self.inv.Binary("-", self.inv.Var("x"), self.inv.IntLit(1)))],
            ),
        ]

        state = self.inv.symbolic_execute(
            stmts,
            {"x": self.inv.Var("x"), "flag": self.inv.Var("flag")},
            ["flag", "x"],
        )

        self.assertEqual(state["x"].to_smt(), "(ite flag (+ 0 1) (- 0 1))")

    def test_verification_conditions_are_implications_over_symbolic_states(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(int n) {
                    int i = 0;
                    while (i < n) {
                        i = i + 1;
                    }
                }
                """,
            )
            formula_path = write_text(Path(tmp) / "formulas.txt", "pre { n >= 0 } candidate { i <= n }")
            problem = self.inv.parse_c_problem(c_path)
            formula_input = self.inv.parse_formula_file(formula_path)

            initialized = self.inv.initialized_vc(problem, formula_input, formula_input.candidates[0])
            preserved = self.inv.preservation_vc(problem, formula_input.candidates[0])

        self.assertTrue(initialized.to_smt().startswith("(=>"))
        self.assertIn("(<= 0 n)", initialized.to_smt())
        self.assertIn("(<= (+ i 1) n)", preserved.to_smt())

    def test_parse_get_value_output_handles_negative_s_expressions(self) -> None:
        raw = "sat\n((__show_x (- 3)) (__show_y 4) (__show_z (+ 1 2)))\n"

        values = self.inv.parse_get_value_output(raw)

        self.assertEqual(values["__show_x"], "-3")
        self.assertEqual(values["__show_y"], "4")
        self.assertEqual(values["__show_z"], "(+ 1 2)")

    def test_validate_formula_variables_reports_unknown_names(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(int n) {
                    int i = 0;
                    while (i < n) {
                        i = i + 1;
                    }
                }
                """,
            )
            formula_path = write_text(Path(tmp) / "formulas.txt", "candidate { missing <= n }")
            problem = self.inv.parse_c_problem(c_path)
            formula_input = self.inv.parse_formula_file(formula_path)

            with self.assertRaisesRegex(self.inv.InvariantError, "missing"):
                self.inv.validate_formula_variables(problem, formula_input)


@unittest.skipUnless(require_z3(), "z3 is required for semantic invariant classification tests")
class InvariantZ3ClassificationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.inv = load_invariants()

    def test_classifies_inductive_and_false_reachable_candidates(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(int n) {
                    int i = 0;
                    while (i < n) {
                        i = i + 1;
                    }
                }
                """,
            )
            formula_path = write_text(
                Path(tmp) / "formulas.txt",
                """
                pre { n >= 0 }
                candidate { i <= n }
                candidate { i == 0 }
                """,
            )
            problem = self.inv.parse_c_problem(c_path)
            formula_input = self.inv.parse_formula_file(formula_path)
            output_variables = self.inv.displayed_variables(problem, formula_input)

            classifications = [
                self.inv.classify_candidate(
                    problem,
                    formula_input,
                    candidate,
                    output_variables,
                    unroll=3,
                    z3_path="z3",
                    timeout=5.0,
                )
                for candidate in formula_input.candidates
            ]

        self.assertEqual(classifications[0].kind, "Inductive invariant")
        self.assertEqual(classifications[1].kind, "Not an invariant")
        self.assertIn("reachable loop-head state", classifications[1].reason)

    def test_modulo_and_division_use_c_truncation_semantics(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "negmod.c",
                """
                void f(int x) {
                    int y = -7;
                    while (x > 0) {
                        x = x - 1;
                    }
                }
                """,
            )
            # In C, -7 % 2 == -1 (truncated); SMT-LIB mod would give 1.
            formula_path = write_text(
                Path(tmp) / "formulas.txt",
                """
                candidate { y % 2 == 1 }
                candidate { y % 2 == -1 }
                candidate { y / 2 == -3 }
                """,
            )
            problem = self.inv.parse_c_problem(c_path)
            formula_input = self.inv.parse_formula_file(formula_path)
            output_variables = self.inv.displayed_variables(problem, formula_input)

            classifications = [
                self.inv.classify_candidate(
                    problem,
                    formula_input,
                    candidate,
                    output_variables,
                    unroll=2,
                    z3_path="z3",
                    timeout=5.0,
                )
                for candidate in formula_input.candidates
            ]

        self.assertEqual(classifications[0].kind, "Not an invariant")
        self.assertEqual(classifications[1].kind, "Inductive invariant")
        self.assertEqual(classifications[2].kind, "Inductive invariant")

    def test_cli_prints_multiple_classifications(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(int n) {
                    int i = 0;
                    while (i < n) {
                        i = i + 1;
                    }
                }
                """,
            )
            formula_path = write_text(
                Path(tmp) / "formulas.txt",
                """
                pre { n >= 0 }
                candidate { i >= 0 }
                candidate { i == 0 }
                """,
            )

            result = run_cli([INVARIANT_SCRIPT, c_path, formula_path, "--z3", "z3", "--unroll", "3"])

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("[Inductive invariant] candidate 1", result.stdout)
        self.assertIn("[Not an invariant] candidate 2", result.stdout)

    def test_cli_reports_formula_errors_with_nonzero_exit(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(int n) {
                    while (n > 0) {
                        n = n - 1;
                    }
                }
                """,
            )
            formula_path = write_text(Path(tmp) / "formulas.txt", "candidate { q >= 0 }")

            result = run_cli([INVARIANT_SCRIPT, c_path, formula_path, "--z3", "z3"])

        self.assertEqual(result.returncode, 2)
        self.assertIn("unknown variable", result.stderr)


if __name__ == "__main__":
    unittest.main()
