# C Coverage Checker

Run:

```sh
python3 coverage_check.py input.c cases.json
```

The checker expects `input.c` to contain exactly one C function. It infers the
function name and parameter types, instruments the function, compiles a small
GCC harness, runs the cases, and reports missing source lines for:

- statement coverage
- decision coverage
- condition coverage
- MC/DC coverage

## Test Cases

`cases.json` can use positional lists:

```json
{
  "cases": [
    [0, 0],
    [4, 2]
  ]
}
```

It can also use parameter names:

```json
{
  "cases": [
    {"a": 0, "b": 0},
    {"a": 4, "b": 2}
  ]
}
```

For one-parameter functions, scalar cases are accepted:

```json
{
  "cases": [0, 1, 2]
}
```

Use JSON numbers and booleans for ordinary primitive values. Use a raw C literal
when you need a suffix, macro, or special constant:

```json
{"$c": "42UL"}
```

Generate a starter file for a new function with:

```sh
python3 coverage_check.py input.c cases.json --init-cases
```

## Notes

- Parameters must be primitive values, with zero to five parameters supported.
- The checker uses GCC and GNU C statement expressions for instrumentation.
- For condition and MC/DC tracking, each atomic condition in a decision is
  evaluated to record its boolean value. Keep decision expressions free of side
  effects such as `i++` if you want results to match the original short-circuit
  behavior exactly.
- `--json` prints a machine-readable report.
- `--keep` leaves the generated instrumented C file in `.coverage_build`.
