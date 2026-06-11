# C Coverage Checkers

This folder contains the coverage-related C analysis scripts and their sample
inputs. The commands below assume you are running them from this directory:

```sh
cd coverage
```

From the repository root, prefix these paths with `coverage/`; for example:

```sh
python3 coverage/coverage_check.py coverage/input.c coverage/cases.json
```

Control-flow coverage:

```sh
python3 coverage_check.py input.c cases.json
```

The checker expects `input.c` to contain exactly one C function. It infers the
function name and parameter types, instruments the function, compiles a small
GCC harness, runs the cases, and reports missing source lines for:

- statement coverage
- branch coverage
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
- Branch coverage tracks the true and false branches of each `if`, loop, and
ternary predicate.
- Instrumentation preserves C's short-circuit evaluation: conditions the
original program would skip are not evaluated and not recorded, so guarded
predicates such as `x != 0 && 100 / x > 2` behave exactly as in the original
program. Skipped conditions appear as unevaluated in the MC/DC observations,
and MC/DC independence pairs treat them as compatible with any value, since
a skipped condition cannot have influenced the decision outcome.
- MC/DC uses the unique-cause criterion: a pair must flip exactly one
evaluated condition together with the decision outcome.
- `--json` prints a machine-readable report.
- `--keep` leaves the generated instrumented C file in `.coverage_build`.

## Data-Flow Coverage

Run:

```sh
python3 data_flow_check.py input.c cases.json
```

The data-flow checker uses the same `input.c` and `cases.json` format. It
builds a small CFG from the function, runs a reaching-definitions analysis to
derive def-use obligations, instruments the function, and reports missing
obligations for:

- all-defs
- all-c-uses
- all-p-uses
- all-du-pairs
- all-p-uses/some-c-uses

The report shows the specific missing data-flow case, for example a definition
line and the c-use or p-use line/outcome that no supplied input covered.
All-du-pairs is the union of the all-c-uses and all-p-uses obligations.

Useful options:

```sh
python3 data_flow_check.py input.c cases.json --json
python3 data_flow_check.py input.c cases.json --keep
```

### Data-Flow Notes

- Parameters and primitive local variables are tracked by name. Avoid shadowing
local variables with the same name in nested scopes.
- C-uses are ordinary computational expression uses. P-uses are variable
occurrences in `if`, `while`, `for`, `do while`, `switch`, and ternary
predicates. Boolean p-use outcomes are tracked as false/true.
- Predicate instrumentation preserves normal C short-circuit evaluation for
variable occurrences. Assignments and `++`/`--` embedded inside expressions
record their definitions at the point of evaluation.
- `switch` models the direct jump from the condition to every `case` label as
well as fallthrough between cases, and the no-`default` path around the body.
- The static obligation set is based on may-reach definitions in the CFG, so it
can include paths that are structurally possible but semantically infeasible.
- Pointers, arrays, structs, and `break`/`continue`-heavy control flow are
intentionally outside the simple generic model.

## Test Case Suggestions

Run on a C file and cases file:

```sh
python3 suggest_tests.py input.c cases.json --criterion mcdc
```

The suggestion tool reuses the same parser and instrumentation, then generates
a bounded set of candidate inputs. In `augment` mode, it suggests the minimum
number of additional cases needed to satisfy the selected criterion over that
generated candidate set. In `replace` mode, it finds a small replacement suite
from the generated domain.

Supported criterion values:

```text
all-defs
all-c-uses
all-p-uses
all-uses
all-c-uses/some-p-uses
all-p-uses/some-c-uses
decision
condition
condition/decision
mcdc
```

For suggestions, `all-uses` means all c-use obligations plus all p-use
outcome obligations. `decision`, `condition`, and `condition/decision` reuse
the control-flow instrumentation and suggest cases that cover missing decision
outcomes, condition values, or both at once.

Examples:

```sh
python3 suggest_tests.py input.c cases.json --criterion all-p-uses
python3 suggest_tests.py input.c cases.json --criterion all-uses
python3 suggest_tests.py input.c cases.json --criterion all-c-uses --mode replace
python3 suggest_tests.py input.c cases.json --criterion decision
python3 suggest_tests.py input.c cases.json --criterion condition
python3 suggest_tests.py input.c cases.json --criterion condition/decision
python3 suggest_tests.py input.c cases.json --criterion mcdc --json
```

The output includes each suggested case as parameter values plus the function
output for that case, followed by entries that can be pasted into `cases.json`.

### Candidate Domains

By default the script generates small primitive domains such as `0`, `1`, `2`,
nearby values from the existing cases, and common integer edge-ish values. For
larger or domain-specific programs, provide a custom domain file:

```json
{
  "a": [0, 1, 2, 4, 6, 8],
  "b": [0, 1, 2, 4, 6, 8]
}
```

Then run:

```sh
python3 suggest_tests.py input.c cases.json --criterion all-p-uses --domain domain.json
```

Useful knobs:

```sh
--values-per-param 18
--max-candidates 5000
--max-additions 8
--timeout 10
--max-timeouts 25
```

Each candidate runs in its own process with its own `--timeout`. A candidate
input that crashes (for example a division by zero) or does not terminate is
skipped and never suggested; after `--max-timeouts` timed-out candidates the
remaining ones are no longer executed.

### Suggestion Limits

This is a bounded generator, not a complete symbolic prover. For data-flow
criteria and ordinary decision, condition, or condition/decision coverage it
solves an exact set-cover problem when the missing target count is small
enough; otherwise it reports that the suite is a greedy approximation. For
MC/DC it searches exact selector pairs over the generated candidate set.

If the script cannot satisfy a criterion, the report lists the still-missing
obligations and hints whether the likely issue is an infeasible objective, a
logically coupled MC/DC condition, or a candidate domain that needs more values.

## Strong Mutation Killing

Run:

```sh
python3 kill_mutant.py input.c mutant.c
```

Both files must contain exactly one compatible C function: the same primitive
parameter types in the same order and the same non-void return type. Function
names do not need to match. The script looks for a strong killing test, meaning
an input where the original function and mutant function both return, but their
return values differ.

Example:

```sh
python3 kill_mutant.py original.c mutant.c
python3 kill_mutant.py original.c mutant.c --engine bounded
python3 kill_mutant.py original.c mutant.c --json
```

The output gives the parameter values, original return value, mutant return
value, and a `cases.json` entry.

The original and mutant files must be a compatible pair. Some sample files in
this directory are used by different exercises and are not intended to be paired
with each other.

Search engines:

```text
auto     try CBMC first, then bounded execution
cbmc     use CBMC only
bounded  execute generated candidate inputs with GCC
```

Useful options:

```sh
--domain domain.json
--cases cases.json
--values-per-param 18
--max-candidates 5000
--unwind 8
--timeout 10
--max-timeouts 25
```

CBMC mode encodes `original_return == mutant_return` as an assertion and asks
CBMC for a counterexample over the generated/domain values. Bounded mode
compiles one harness and runs one candidate per process, so nonterminating
mutant inputs are skipped after `--timeout`. If no killing case is found, the
mutant may be equivalent, the predicate change may only cause nontermination,
or the domain/unwind bound may need to be increased.