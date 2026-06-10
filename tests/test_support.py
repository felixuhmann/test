from __future__ import annotations

import importlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
HOARE_SCRIPT = REPO_ROOT / "Hoare" / "annotate_c.py"
INVARIANT_SCRIPT = REPO_ROOT / "Invariants" / "invariant_classifier.py"
COVERAGE_DIR = REPO_ROOT / "coverage"
COVERAGE_CHECK_SCRIPT = COVERAGE_DIR / "coverage_check.py"
DATA_FLOW_SCRIPT = COVERAGE_DIR / "data_flow_check.py"
SUGGEST_TESTS_SCRIPT = COVERAGE_DIR / "suggest_tests.py"
KILL_MUTANT_SCRIPT = COVERAGE_DIR / "kill_mutant.py"


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Could not load module {name} from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def load_hoare():
    return load_module("hoare_annotate_c_under_test", HOARE_SCRIPT)


def load_invariants():
    return load_module("invariant_classifier_under_test", INVARIANT_SCRIPT)


def load_coverage_check():
    add_coverage_to_path()
    return importlib.import_module("coverage_check")


def load_data_flow_check():
    add_coverage_to_path()
    load_coverage_check()
    return importlib.import_module("data_flow_check")


def load_suggest_tests():
    add_coverage_to_path()
    load_coverage_check()
    load_data_flow_check()
    return importlib.import_module("suggest_tests")


def load_kill_mutant():
    add_coverage_to_path()
    load_coverage_check()
    load_suggest_tests()
    return importlib.import_module("kill_mutant")


def add_coverage_to_path() -> None:
    path = str(COVERAGE_DIR)
    if path not in sys.path:
        sys.path.insert(0, path)


def run_cli(args: list[str | Path], *, cwd: Path | None = None, timeout: float = 30.0) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["PYTHONPATH"] = os.pathsep.join(
        part
        for part in [
            str(COVERAGE_DIR),
            str(REPO_ROOT),
            env.get("PYTHONPATH", ""),
        ]
        if part
    )
    return subprocess.run(
        [sys.executable, *(str(arg) for arg in args)],
        cwd=str(cwd or REPO_ROOT),
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
        check=False,
    )


def write_text(path: Path, text: str) -> Path:
    path.write_text(text.strip() + "\n", encoding="utf-8")
    return path


def write_json(path: Path, value: Any) -> Path:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    return path


def require_gcc() -> bool:
    return shutil.which("gcc") is not None


def require_z3() -> bool:
    return shutil.which("z3") is not None
