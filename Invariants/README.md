# Invariant Classifier

Run:

```sh
python3 Invariants/invariant_classifier.py Invariants/input.c Invariants/invariant.txt
```

The formula file can contain a single formula:

```text
{(b > x) => (a > y)}
```

It can also contain several candidates and an optional stronger reachable fact:

```text
reachable { a >= b && x >= y }
candidate { (b > x) => (a > y) }
candidate { a >= b && x >= y }
```

The classifier reports:

- `Inductive invariant` when the candidate is initialized and preserved by the loop body.
- `Non-inductive invariant` when it holds at all reachable loop-head states but the Hoare triple `{candidate && guard} body {candidate}` fails.
- `Not an invariant` when a reachable loop-head state falsifies it.
- `Unknown` when the candidate is initialized and not inductive, but the available reachability checks cannot prove or refute invariance.

The C model is intentionally small: one function, one top-level `while`, scalar integer/boolean variables, assignments, and `if` statements. Integer arithmetic is modeled as mathematical integer arithmetic, not C overflow.
