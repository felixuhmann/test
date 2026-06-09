# Hoare Logic VC Checker

`hoare_solver.py` checks small annotated while-programs. It implements the
standard assignment, skip, sequence, conditional, while, and consequence-style
annotation rules by computing weakest preconditions and sending the resulting
verification conditions to the `z3` command-line solver.

`invariant_classifier.py` classifies worksheet-style candidate loop invariants
as:

- `Inductive invariant`
- `Non-inductive invariant`
- `Neither`
- `Unknown` when the available checks are insufficient

Run all included examples:

```sh
python3 Hoare/hoare_solver.py Hoare/examples/*.hl
```

Classify the included invariant worksheets:

```sh
python3 Hoare/invariant_classifier.py Hoare/examples/worksheet_*.inv
```

Print the generated rule premises and formulas:

```sh
python3 Hoare/hoare_solver.py --verbose Hoare/examples/sqrt.hl
```

Print a lecture-style annotated solution:

```sh
python3 Hoare/hoare_solver.py --annotate Hoare/examples/binary_search.hl
python3 Hoare/hoare_solver.py --annotate --no-annotation-comments Hoare/examples/binary_search.hl
```

Input format:

```text
vars int x, y;
vars bool b;

pre { x >= 0 }

x = x + 1;
if (x > y) {
  y = x;
} else {
  skip;
}

while (x < 10)
invariant { y >= x }
{
  x = x + 1;
}

post { y >= 0 }
```

Assertions can be inserted as proof cut-points:

```text
assert { y >= x };
```

Lecture-style bare assertions are accepted too:

```text
{ y >= x }
```

Lecture-style syntax is also supported:

```text
{0 <= target && target <= n}
lo := 0
hi := n
while lo < hi do
    mid := (lo + hi) / 2
    if mid < target then
        lo := mid + 1
    else
        hi := mid
    fi
od
{lo == target}
```

Loops need invariants. Write them as:

```text
while x < 10 invariant { y >= x } do
    x := x + 1
od
```

The only missing-invariant heuristic currently built in is the common binary
search range pattern above, where `while lo < hi` and final `lo == target`
produce the candidate invariant `lo <= target && target <= hi`.

This is a partial-correctness checker. It proves that the postcondition holds if
the program terminates; it does not prove loop termination unless you encode a
separate variant argument yourself.

## Invariant classifier input

The `.inv` format is deliberately close to the worksheet programs:

```text
vars int a, b;
vars nat i;
vars bool flag;

pre { true }

init {
  a = b + 1;
}

while (a > 0) {
  a = a - 1;
}

reachable { a >= 0 }

candidate { a >= 0 }
candidate { a != 3 }
```

`reachable { ... }` is optional. If provided, the classifier first proves that
the reachable fact is initialized and preserved. It then uses that fact to prove
that a candidate is an invariant even when the candidate itself is not
inductive.

Without a reachable fact, the classifier still proves inductive invariants and
finds many `Neither` cases by symbolic unrolling. It may return `Unknown` for a
candidate that is initialized but not inductive and has no reachable
counterexample within the configured unroll bound.

Useful options:

```sh
python3 Hoare/invariant_classifier.py --unroll 50 Hoare/examples/worksheet_bool.inv
python3 Hoare/invariant_classifier.py --timeout 2 Hoare/examples/worksheet_mod.inv
```
