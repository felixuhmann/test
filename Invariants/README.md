# Invariant Classifier

This directory contains a small Z3-backed checker for classifying candidate loop
invariants for simple C functions.

The intended workflow is:

1. Put the C function in `input.c`.
2. Put one or more candidate formulas in a separate text file.
3. Run `invariant_classifier.py`.
4. Read whether each candidate is inductive, non-inductive but still invariant,
   not an invariant, or unknown.

## Quick Start

Run the included example:

```sh
python3 Invariants/invariant_classifier.py Invariants/input.c Invariants/invariant.txt
```

The bundled `input.c` contains:

```c
void function(int x, int y) {
    int i, j;
    i = x ;
    j = y ;
    while ( i > 1) {
        i = i / 2;
        j = j * 2;
    }
}
```

The bundled `invariant.txt` contains:

```text
{i*j>0}
```

For that candidate, the tool reports `Not an invariant`: without a
precondition on the inputs, the formula can already be false at the initial
loop-head state (for example `x = -8, y = 5`).

The worked example used in the rest of this README is:

```c
void function(int a, int b, int x, int y) {
    int tmp;

    if (b >= a) {
        tmp = a;
        a = b + 1;
        b = tmp;
    }

    if (y >= x) {
        tmp = x;
        x = y + 1;
        y = tmp;
    }

    while (a != b && x != y) {
        a = a - 1;
        y = y + 1;
    }
}
```

For that program, the candidate `{(b > x) => (a > y)}` is classified as
`Non-inductive invariant`: the formula holds at all reachable loop-head
states, but it is not preserved from every state satisfying only the
candidate and the loop guard.

## Requirements

The script uses:

- Python 3
- `pycparser`
- the `z3` command-line executable

Check that Z3 is available with:

```sh
command -v z3
```

If Z3 is installed somewhere else, pass it explicitly:

```sh
python3 Invariants/invariant_classifier.py Invariants/input.c Invariants/invariant.txt \
  --z3 /path/to/z3
```

## Input C Format

The C file must contain exactly one function and exactly one top-level `while`
loop in the function body.

Statements before the `while` are treated as the loop initialization. The
candidate invariant is checked at the loop head, after initialization and before
each possible loop-body execution.

Supported C features:

- scalar integer and boolean parameters/local variables
- local variable declarations, with or without initializers
- assignments such as `x = y + 1`
- compound assignments such as `x += 1`
- `if` / `else`
- one top-level `while`
- arithmetic `+`, `-`, `*`, `/`, `%`
- comparisons `<`, `<=`, `>`, `>=`, `==`, `!=`
- boolean connectives `&&`, `||`, `!`

Unsupported features include nested `while` loops, `for` loops, arrays,
pointers, structs, function calls, floating-point arithmetic, `break`,
`continue`, and `return` before the target loop.

Integer arithmetic is modeled as mathematical integer arithmetic. C overflow,
machine integer widths, and undefined behavior are not modeled. Division and
modulo follow C semantics (truncation toward zero, so `-7 / 2 == -3` and
`-7 % 2 == -1`), not the SMT-LIB Euclidean definitions.

## Formula Files

A formula file may contain a single braced formula:

```text
{(b > x) => (a > y)}
```

It may also contain multiple candidates:

```text
candidate { (b > x) => (a > y) }
candidate { a >= b && x >= y }
candidate { a > y }
```

The keywords `candidate` and `invariant` are equivalent for candidate formulas:

```text
invariant { a >= b && x >= y }
```

You can optionally add a precondition on the original function inputs:

```text
pre { a >= 0 && b >= 0 && x >= 0 && y >= 0 }
candidate { a >= b && x >= y }
```

You can also provide a stronger reachable fact:

```text
reachable { a >= b && x >= y }
candidate { (b > x) => (a > y) }
```

A reachable fact is useful when a candidate is not inductive by itself but
follows from a stronger invariant. The tool first checks that the reachable fact
is initialized and preserved. If it is valid and implies the candidate, the
candidate can be classified as a non-inductive invariant.

## Formula Syntax

Use C-like syntax:

- implication: `=>`
- conjunction: `&&`
- disjunction: `||`
- negation: `!`
- equality: `==` or `=`
- disequality: `!=`
- comparisons: `<`, `<=`, `>`, `>=`
- arithmetic: `+`, `-`, `*`, `/`, `%`
- constants: integers, `true`, `false`

Examples:

```text
{a >= b && x >= y}
{(b > x) => (a > y)}
{!(a == b) || x >= y}
{(a - b) <= 2 * (x - y)}
```

All variables mentioned in the formula must be parameters or local variables in
`input.c`.

## Classifications

The tool reports one of four outcomes for each candidate.

`Inductive invariant`

The candidate is true at every initial loop-head state and is preserved by one
loop-body step whenever the candidate and loop guard are true:

```text
{candidate && guard} loop_body {candidate}
```

For the sample program:

```text
{a >= b && x >= y}
```

is inductive.

`Non-inductive invariant`

The candidate holds at all reachable loop-head states, but the one-step Hoare
triple fails from some unreachable or overly weak state satisfying only
`candidate && guard`.

For the sample program:

```text
{(b > x) => (a > y)}
```

is non-inductive. A typical witness is:

```text
before: a=2, b=1, x=0, y=1
after:  a=1, b=1, x=0, y=2
```

The `before` state satisfies the candidate and the loop guard. After executing
the loop body once, the candidate is false. This proves the candidate is not
inductive. The state is not reachable from the function initialization, so the
candidate can still be an invariant.

`Not an invariant`

The candidate is false at some reachable loop-head state. The report prints
example input values and the reachable state that violates the formula.

For the sample program:

```text
{a > y}
```

is not an invariant because it can be false immediately after initialization.

`Unknown`

The candidate is initialized and not inductive, but the checker could not prove
that it holds on every reachable loop-head state and could not find a reachable
counterexample within the configured checks.

This is expected for some programs. Proving arbitrary invariants is undecidable,
so the classifier intentionally reports `Unknown` instead of guessing.

## Reachability Checks

The tool uses three layers:

1. Z3 checks whether the candidate is initialized.
2. Z3 checks whether the candidate is preserved by one loop-body step.
3. If preservation fails, the tool searches for reachable counterexamples.

Reachable counterexample search has two parts:

- bounded symbolic unrolling, controlled by `--unroll`
- a closed-form check for loops where every variable changes by a constant per
  iteration

The sample loop has constant updates:

```c
a = a - 1;
y = y + 1;
```

so the closed-form check can prove some non-inductive candidates are still true
on all reachable loop-head states.

For more complex loops, add a `reachable { ... }` fact when you know a stronger
invariant that explains why the candidate holds.

## Command-Line Options

```sh
python3 Invariants/invariant_classifier.py INPUT_C FORMULA_FILE [options]
```

Options:

- `--z3 PATH`: use a specific Z3 executable
- `--unroll N`: number of loop iterations to symbolically unroll before the
  closed-form reachability attempt; default is `20`
- `--timeout SECONDS`: per-query Z3 timeout; default is `10.0`

Examples:

```sh
python3 Invariants/invariant_classifier.py Invariants/input.c Invariants/invariant.txt
python3 Invariants/invariant_classifier.py Invariants/input.c my_formula.txt --unroll 50
python3 Invariants/invariant_classifier.py Invariants/input.c my_formula.txt --timeout 2
```

## Example Formula Files

Inductive candidate:

```text
{a >= b && x >= y}
```

Non-inductive invariant:

```text
{(b > x) => (a > y)}
```

Not an invariant:

```text
{a > y}
```

Several candidates in one file:

```text
candidate { (b > x) => (a > y) }
candidate { a >= b && x >= y }
candidate { a > y }
```

Using a reachable fact:

```text
reachable { a >= b && x >= y }
candidate { (b > x) => (a > y) }
```

## Troubleshooting

`expected expression`

The formula has a syntax error, such as a missing variable or malformed
comparison:

```text
{(a >= b) && (x >= <)}
```

`formula references unknown variable`

The formula mentions a name that is not a parameter or local variable in
`input.c`.

`expected exactly one top-level while loop`

The function has no top-level `while`, more than one top-level `while`, or the
loop is nested inside another statement.

`Unknown`

The checker needs more information. Try increasing `--unroll`, simplifying the
program, or adding a valid `reachable { ... }` fact.
