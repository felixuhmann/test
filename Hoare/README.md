# Hoare C Annotator

`annotate_c.py` generates lecture-style Hoare annotations for a small subset of
C programs. It is meant for worksheet-style partial-correctness proofs where the
user already knows the loop invariant and wants the surrounding assertions and
rule comments filled in.

The typical input is:

1. A C file containing exactly one function.
2. A loop invariant such as `{l*l <= n < r*r}`.
3. Optionally, a precondition and final postcondition.

The output is an annotated version of the program with assertions and comments
such as:

```c
{ l * l <= n && n < r * r }
// invariant

while (l != r - 1) {
    { l * l <= n && n < r * r && l != r - 1 }
    // while rule

    m = (l + r) / 2;

    { l * l <= n && n < r * r }
    // assignment rule
}
```

## Tools Used

The implementation intentionally reuses existing tools where they help:

- `pycparser` parses the C function, so we do not hand-write a C parser.
- Z3 is used, when available, to recognize simple implication/consequence steps
  and keep the printed annotations shorter.

Tools such as Frama-C/WP and CBMC can verify C programs with annotations, but
they do not directly generate the lecture-style proof script expected here.
This project therefore uses them only as inspiration and keeps the generator
small.

## Requirements

Required:

```sh
python3
python3 -c 'import pycparser'
```

Recommended:

```sh
z3 --version
```

If Z3 is missing, the annotator can still run, but some consequence annotations
may be less compact.

## Quick Start

Run the included integer-square-root example:

```sh
python3 Hoare/annotate_c.py Hoare/examples/sqrt.c '{l*l <= n < r*r}' --pre '{n >= 0}'
```

Write the annotated program to a file:

```sh
python3 Hoare/annotate_c.py Hoare/examples/sqrt.c '{l*l <= n < r*r}' \
  --pre '{n >= 0}' \
  --output Hoare/examples/sqrt.annotated.c
```

Disable Z3-assisted simplification:

```sh
python3 Hoare/annotate_c.py Hoare/examples/sqrt.c '{l*l <= n < r*r}' --no-z3
```

## Command Reference

```sh
python3 Hoare/annotate_c.py C_FILE INVARIANT [options]
```

Arguments:

- `C_FILE`: path to a C file containing exactly one function.
- `INVARIANT`: an inline assertion or a path to a text file containing one.

Options:

- `--pre ASSERTION`: optional initial precondition.
- `--post ASSERTION`: optional final postcondition.
- `--output PATH`, `-o PATH`: write output to a file instead of stdout.
- `--z3 PATH`: use a specific Z3 executable.
- `--timeout SECONDS`: per-query timeout for Z3.
- `--no-z3`: skip Z3 entirely.

`--pre`, `--post`, and `INVARIANT` can all be written either with or without
outer braces.

## Supported C Subset

The current generator supports the subset used in the course examples:

- Exactly one C function per input file.
- `int` parameters.
- Local `int` variable declarations.
- Assignments to simple variables, for example `x = y + 1;`.
- Arithmetic operators: `+`, `-`, `*`, `/`, `%`.
- Comparisons: `<`, `<=`, `>`, `>=`, `==`, `!=`.
- Boolean operators in C expressions: `&&`, `||`, `!`.
- `if (...) { ... } else { ... }`.
- Exactly one `while (...) { ... }` loop.

The tool assumes all program variables are mathematical integers in the proof.
It does not model fixed-width C overflow.

Unsupported constructs include:

- Multiple loops or nested loops.
- `for`, `do while`, `switch`, `break`, `continue`.
- Function calls.
- Arrays, pointers, structs, and casts with semantic meaning.
- Compound assignments such as `+=`.
- Increment/decrement operators such as `i++`.
- Return-value reasoning.

## Assertion Syntax

Assertions use a C-like mathematical syntax:

```text
{ n >= 0 }
{ l*l <= n < r*r }
{ x == y || !(x < y) }
```

Supported assertion operators:

- Arithmetic: `+`, `-`, `*`, `/`, `%`.
- Comparisons: `<`, `<=`, `>`, `>=`, `==`, `!=`, `=`.
- Boolean connectives: `&&`, `||`, `!`, `and`, `or`, `not`.
- Implication: `=>`.

Chained comparisons are treated mathematically. For example:

```text
{l*l <= n < r*r}
```

is parsed as:

```text
{l * l <= n && n < r * r}
```

## Example

Input C file:

```c
void function(int n) {
    int l = 0;
    int r = n + 1;
    int m;

    while (l != r - 1) {
        m = (l + r) / 2;

        if (m * m <= n) {
            l = m;
        } else {
            r = m;
        }
    }
}
```

Command:

```sh
python3 Hoare/annotate_c.py Hoare/examples/sqrt.c '{l*l <= n < r*r}' --pre '{n >= 0}'
```

The annotator computes the weakest precondition needed before each assignment,
inserts the invariant at the loop head, adds branch assumptions for conditionals,
and prints the rule that justifies each assertion.

If no `--post` is given, the tool derives the natural loop-exit assertion. For
the guard `l != r - 1`, it prints:

```text
{ l * l <= n && n < r * r && !(l != r - 1) }
// while rule

{ l * l <= n && n < r * r && l == r - 1 }
// consequence rule

{ l * l <= n && n < r * r && r == l + 1 }
// consequence rule

{ l * l <= n && n < (l + 1) * (l + 1) }
// consequence rule
```

## How The Output Is Built

The generator uses standard Hoare-logic rules:

- Assignment: compute the weakest precondition by substituting the assigned
  expression into the postcondition.
- Sequence: pass each statement's postcondition backwards to the previous
  statement.
- Conditional: annotate the then-branch with `condition` and the else-branch
  with `!condition`.
- While: use the supplied invariant before the loop, inside the loop, and at
  loop exit with the negated guard.
- Consequence: print intermediate assertions when the proof needs strengthening
  or weakening.

The tool does not prove that the invariant is correct in a fully general way.
It generates the annotated proof skeleton and uses Z3 only for small implication
checks that improve readability.

## Troubleshooting

`could not parse C input`

The C file likely uses syntax outside pycparser's direct subset or contains
preprocessor directives. Keep the input as a plain function without includes or
macros.

`expected exactly one while loop`

The current renderer is intentionally scoped to one loop. Split the example or
extend the renderer before using programs with multiple loops.

`assertion mentions unknown variable`

The invariant, precondition, or postcondition refers to a name that is not a
function parameter or local variable in the C file.

Unexpected arithmetic behavior

Assertions are interpreted over mathematical integers. C overflow, unsigned
arithmetic, and machine integer widths are intentionally ignored.

## Project Scope

This tool is a small proof-annotation generator, not a production verifier. The
goal is to write as little custom code as possible while still producing the
specific annotated output format used in Hoare-logic exercises.
