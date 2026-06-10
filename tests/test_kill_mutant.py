from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from test_support import KILL_MUTANT_SCRIPT, load_kill_mutant, require_gcc, run_cli, write_text


class KillMutantUtilityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.kill = load_kill_mutant()

    def test_clone_with_name_renames_function_and_recursive_calls(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            c_path = write_text(
                Path(tmp) / "fib.c",
                """
                int fib(int n) {
                    if (n <= 1) {
                        return n;
                    }
                    return fib(n - 1) + fib(n - 2);
                }
                """,
            )
            _, _, function = self.kill.parse_c_file(c_path)

            renamed = self.kill.clone_with_name(function, self.kill.ORIGINAL_NAME)
            rendered = self.kill.render_functions(renamed, renamed)

        self.assertIn("int __kill_original(int n)", rendered)
        self.assertIn("__kill_original(n - 1)", rendered)
        self.assertNotIn("fib(n - 1)", rendered)

    def test_compatible_signatures_accepts_matching_primitive_functions(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            original = write_text(Path(tmp) / "original.c", "long f(int x, _Bool ok) { return ok ? x : -x; }")
            mutant = write_text(Path(tmp) / "mutant.c", "long g(int y, _Bool flag) { return flag ? y : -y; }")
            _, _, original_function = self.kill.parse_c_file(original)
            _, _, mutant_function = self.kill.parse_c_file(mutant)

            params, return_type = self.kill.compatible_signatures(original_function, mutant_function)

        self.assertEqual([param.type_name for param in params], ["int", "_Bool"])
        self.assertEqual(return_type, "long")

    def test_compatible_signatures_rejects_parameter_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            original = write_text(Path(tmp) / "original.c", "int f(int x) { return x; }")
            mutant = write_text(Path(tmp) / "mutant.c", "int g(long x) { return (int)x; }")
            _, _, original_function = self.kill.parse_c_file(original)
            _, _, mutant_function = self.kill.parse_c_file(mutant)

            with self.assertRaisesRegex(SystemExit, "Parameter type mismatch"):
                self.kill.compatible_signatures(original_function, mutant_function)

    def test_compatible_signatures_rejects_void_return_type(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            original = write_text(Path(tmp) / "original.c", "void f(int x) { x = x + 1; }")
            mutant = write_text(Path(tmp) / "mutant.c", "void g(int x) { x = x + 2; }")
            _, _, original_function = self.kill.parse_c_file(original)
            _, _, mutant_function = self.kill.parse_c_file(mutant)

            with self.assertRaisesRegex(SystemExit, "void functions"):
                self.kill.compatible_signatures(original_function, mutant_function)

    def test_output_format_and_cbmc_value_conversion_cover_common_types(self) -> None:
        bool_fmt, bool_args = self.kill.output_format("_Bool", "value")
        unsigned_fmt, unsigned_args = self.kill.output_format("unsigned int", "value")
        signed_fmt, signed_args = self.kill.output_format("int", "value")

        self.assertEqual(bool_fmt, "%s")
        self.assertEqual(bool_args, ['value ? "true" : "false"'])
        self.assertEqual(unsigned_fmt, "%llu")
        self.assertEqual(unsigned_args, ["(unsigned long long)value"])
        self.assertEqual(signed_fmt, "%lld")
        self.assertEqual(signed_args, ["(long long)value"])
        self.assertTrue(self.kill.convert_cbmc_value("1", "_Bool"))
        self.assertEqual(self.kill.convert_cbmc_value("-42", "int"), -42)
        self.assertEqual(self.kill.convert_cbmc_value("3.5f", "float"), 3.5)

    def test_parse_kill_output_returns_first_killing_case(self) -> None:
        result = self.kill.parse_kill_output("noise\nK 1 4 5\nK 2 6 7\n", [[0], [3], [5]], "bounded")

        self.assertIsNotNone(result)
        assert result is not None
        self.assertTrue(result.killed)
        self.assertEqual(result.inputs, [3])
        self.assertEqual(result.original_output, "4")
        self.assertEqual(result.mutant_output, "5")
        self.assertEqual(result.engine, "bounded")

    def test_result_to_json_maps_inputs_by_parameter_name(self) -> None:
        params = [SimpleNamespace(name="x")]
        result = self.kill.KillResult(
            killed=True,
            inputs=[2],
            original_output="3",
            mutant_output="4",
            engine="bounded",
            hints=[],
        )

        payload = self.kill.result_to_json(result, params)

        self.assertEqual(payload["inputs"], {"x": 2})
        self.assertEqual(payload["case"], [2])
        self.assertEqual(payload["original_output"], "3")


@unittest.skipUnless(require_gcc(), "gcc is required for bounded mutation-killing tests")
class KillMutantCliIntegrationTests(unittest.TestCase):
    def test_bounded_cli_finds_strong_killing_case(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            original = write_text(tmp_path / "original.c", "int f(int x) { return x + 1; }")
            mutant = write_text(tmp_path / "mutant.c", "int f(int x) { return x + 2; }")

            result = run_cli(
                [
                    KILL_MUTANT_SCRIPT,
                    original,
                    mutant,
                    "--engine",
                    "bounded",
                    "--json",
                    "--values-per-param",
                    "2",
                    "--max-candidates",
                    "4",
                    "--timeout",
                    "5",
                ],
                timeout=20,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertTrue(payload["killed"])
        self.assertEqual(payload["engine"], "bounded")
        self.assertNotEqual(payload["original_output"], payload["mutant_output"])

    def test_bounded_cli_reports_surviving_equivalent_mutant(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            original = write_text(tmp_path / "original.c", "int f(int x) { return x + 1; }")
            mutant = write_text(tmp_path / "mutant.c", "int g(int x) { return x + 1; }")

            result = run_cli(
                [
                    KILL_MUTANT_SCRIPT,
                    original,
                    mutant,
                    "--engine",
                    "bounded",
                    "--json",
                    "--values-per-param",
                    "2",
                    "--max-candidates",
                    "4",
                    "--timeout",
                    "5",
                ],
                timeout=20,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertFalse(payload["killed"])
        self.assertIn("No candidate produced", payload["hints"][0])


if __name__ == "__main__":
    unittest.main()
