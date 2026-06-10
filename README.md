# Program Analysis Tools

This repository contains small tools and notes for program analysis exercises.

## Quick Start

Run the bundled examples from the repository root:

```sh
python3 coverage/coverage_check.py coverage/input.c coverage/cases.json
python3 coverage/data_flow_check.py coverage/input.c coverage/cases.json
python3 Hoare/annotate_c.py Hoare/examples/sqrt.c '{l*l <= n < r*r}' --pre '{n >= 0}'
python3 Invariants/invariant_classifier.py Invariants/input.c Invariants/invariant.txt
```

Other coverage tools use the same repository-root path style:

```sh
python3 coverage/suggest_tests.py path/to/input.c path/to/cases.json --criterion mcdc
python3 coverage/kill_mutant.py path/to/original.c path/to/mutant.c --engine bounded
```

## Folders

- `coverage/`: dynamic C coverage checkers, data-flow coverage analysis, test
  case suggestion, and strong mutation-killing utilities.
- `Hoare/`: a lecture-style Hoare annotation generator for a small subset of C.
- `Invariants/`: a Z3-backed loop invariant classifier for simple C functions.
- `kripke/`: short notes on temporal-logic operators over Kripke structures.

Each tool folder contains its own README or summary with usage details.
