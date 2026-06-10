from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from test_support import HOARE_SCRIPT, load_hoare, run_cli, write_text


class HoareAssertionParserTests(unittest.TestCase):
    def setUp(self) -> None:
        self.hoare = load_hoare()

    def test_chained_comparison_is_expanded_mathematically(self) -> None:
        expr = self.hoare.parse_assertion("{ l*l <= n < r*r }")

        self.assertEqual(self.hoare.pretty(expr), "l * l <= n && n < r * r")
        self.assertEqual(expr.to_smt(), "(and (<= (* l l) n) (< n (* r r)))")

    def test_words_and_c_style_boolean_connectives_are_supported(self) -> None:
        expr = self.hoare.parse_assertion("not (x = y) or x != 0")

        self.assertEqual(self.hoare.pretty(expr), "!(x == y) || x != 0")
        self.assertEqual(expr.variables(), {"x", "y"})

    def test_precedence_and_implication_are_right_associative(self) -> None:
        expr = self.hoare.parse_assertion("a > 0 && b > 0 => c > 0 => d > 0")

        self.assertEqual(
            self.hoare.pretty(expr),
            "a > 0 && b > 0 => c > 0 => d > 0",
        )
        self.assertIn("(=> (and (> a 0) (> b 0))", expr.to_smt())

    def test_bad_assertion_text_reports_location_context(self) -> None:
        with self.assertRaisesRegex(self.hoare.AnnotatorError, "unexpected assertion text"):
            self.hoare.parse_assertion("x >= 0 @ y >= 0")


class HoareProgramParsingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.hoare = load_hoare()

    def test_parse_small_supported_c_subset(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "program.c",
                """
                void f(int n) {
                    // comments are ignored before pycparser sees the input
                    int i = 0;
                    int step = 1;
                    while (i != n) {
                        if (i < n) {
                            i = i + step;
                        } else {
                            i = i - step;
                        }
                    }
                }
                """,
            )

            program = self.hoare.parse_c_program(c_path)

        self.assertEqual(program.name, "f")
        self.assertEqual(program.params, ["n"])
        self.assertEqual(program.variables, {"n", "i", "step"})
        self.assertIsInstance(program.body[0], self.hoare.Assign)
        self.assertIsInstance(program.body[2], self.hoare.While)
        loop = program.body[2]
        self.assertEqual(self.hoare.pretty(loop.cond), "i != n")
        self.assertIsInstance(loop.body[0], self.hoare.If)

    def test_rejects_non_integer_parameters(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "bad.c",
                """
                void f(long n) {
                    while (n != 0) {
                        n = n - 1;
                    }
                }
                """,
            )

            with self.assertRaisesRegex(self.hoare.AnnotatorError, "parameter n must be an int"):
                self.hoare.parse_c_program(c_path)

    def test_rejects_unsupported_statements(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "bad.c",
                """
                int f(int n) {
                    while (n != 0) {
                        return n;
                    }
                    return 0;
                }
                """,
            )

            with self.assertRaisesRegex(self.hoare.AnnotatorError, "unsupported C statement: Return"):
                self.hoare.parse_c_program(c_path)


class HoareWeakestPreconditionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.hoare = load_hoare()

    def test_assignment_weakest_precondition_substitutes_expression(self) -> None:
        post = self.hoare.parse_assertion("x + y <= n")
        stmt = self.hoare.Assign("x", self.hoare.Binary("+", self.hoare.Var("y"), self.hoare.IntLit(1)))

        pre = self.hoare.wp_stmt(stmt, post)

        self.assertEqual(self.hoare.pretty(pre), "y + 1 + y <= n")

    def test_if_weakest_precondition_combines_both_branches(self) -> None:
        post = self.hoare.parse_assertion("x >= 0")
        stmt = self.hoare.If(
            self.hoare.Var("flag"),
            [self.hoare.Assign("x", self.hoare.IntLit(1))],
            [self.hoare.Assign("x", self.hoare.IntLit(-1))],
        )

        pre = self.hoare.wp_stmt(stmt, post)

        self.assertEqual(
            self.hoare.pretty(pre),
            "(flag => 1 >= 0) && (!flag => -1 >= 0)",
        )

    def test_loop_without_attached_invariant_is_an_error(self) -> None:
        stmt = self.hoare.While(self.hoare.Var("keep_going"), [])

        with self.assertRaisesRegex(self.hoare.AnnotatorError, "no invariant"):
            self.hoare.wp_stmt(stmt, self.hoare.BoolLit(True))


class HoareRendererAndCliTests(unittest.TestCase):
    def setUp(self) -> None:
        self.hoare = load_hoare()

    def test_renderer_inserts_invariant_and_loop_exit_consequence(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(int n) {
                    int i = 0;
                    while (i != n) {
                        i = i + 1;
                    }
                }
                """,
            )
            program = self.hoare.parse_c_program(c_path)
            invariant = self.hoare.parse_assertion("0 <= i && i <= n")
            program = self.hoare.dataclasses.replace(
                program,
                body=self.hoare.with_invariant(program.body, invariant),
            )

            rendered = self.hoare.Renderer(checker=None).render(
                program,
                self.hoare.parse_assertion("n >= 0"),
                None,
            )

        self.assertIn("{ 0 <= i && i <= n }\n// invariant", rendered)
        self.assertIn("while (i != n) {", rendered)
        self.assertIn("{ 0 <= i && i <= n && i == n }\n// consequence rule", rendered)

    def test_renderer_rejects_programs_with_more_than_one_loop(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "two_loops.c",
                """
                void f(int n) {
                    while (n != 0) {
                        n = n - 1;
                    }
                    while (n != 1) {
                        n = n + 1;
                    }
                }
                """,
            )
            program = self.hoare.parse_c_program(c_path)
            invariant = self.hoare.parse_assertion("n >= 0")
            program = self.hoare.dataclasses.replace(
                program,
                body=self.hoare.with_invariant(program.body, invariant),
            )

            with self.assertRaisesRegex(self.hoare.AnnotatorError, "expected exactly one while loop"):
                self.hoare.Renderer(checker=None).render(program, None, None)

    def test_cli_writes_output_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            c_path = write_text(
                tmp_path / "counter.c",
                """
                void f(int n) {
                    int i = 0;
                    while (i != n) {
                        i = i + 1;
                    }
                }
                """,
            )
            out_path = tmp_path / "annotated.c"

            result = run_cli(
                [
                    HOARE_SCRIPT,
                    c_path,
                    "{0 <= i && i <= n}",
                    "--pre",
                    "{n >= 0}",
                    "--no-z3",
                    "--output",
                    out_path,
                ]
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, "")
            output = out_path.read_text(encoding="utf-8")
            self.assertIn("// while rule", output)
            self.assertIn("i = i + 1;", output)

    def test_cli_reports_unknown_assertion_variables(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "counter.c",
                """
                void f(int n) {
                    while (n != 0) {
                        n = n - 1;
                    }
                }
                """,
            )

            result = run_cli([HOARE_SCRIPT, c_path, "{q >= 0}", "--no-z3"])

            self.assertEqual(result.returncode, 2)
            self.assertIn("unknown variable", result.stderr)


if __name__ == "__main__":
    unittest.main()
