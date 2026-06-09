# Hoare C Annotator

`annotate_c.py` generates lecture-style Hoare annotations for a small integer C
subset: local `int` variables, assignments, `if/else`, and one `while` loop.

It uses:

- `pycparser` to parse the C function.
- Z3, when available, to choose shorter consequence annotations.

Run the square-root example:

```sh
python3 Hoare/annotate_c.py Hoare/examples/sqrt.c '{l*l <= n < r*r}' --pre '{n >= 0}'
```

Write the result to a file:

```sh
python3 Hoare/annotate_c.py Hoare/examples/sqrt.c '{l*l <= n < r*r}' \
  --pre '{n >= 0}' \
  --output Hoare/examples/sqrt.annotated.c
```

If `--pre` is omitted, the tool starts with the weakest precondition needed to
establish the invariant. If `--post` is omitted, it prints the loop-exit
assertion and, for guards like `l != r - 1`, derives the common final
substitution step automatically.

The assertion parser treats chained comparisons mathematically, so:

```text
{l*l <= n < r*r}
```

is parsed as:

```text
{l * l <= n && n < r * r}
```

This is a generator for teaching annotations, not a full C verifier. It assumes
mathematical integer arithmetic for assertions and supports only the C subset
listed above.
