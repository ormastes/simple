# A local variable named `grid` is hijacked by the grid-literal parser

Status: OPEN — found 2026-08-09 while building
`scripts/check/check_engine_differential.spl`. Parser-level, so it affects
every engine equally (this is NOT an engine divergence).

## Summary

`grid` behaves as a de-facto reserved word that is not documented as reserved.
Naming an ordinary local variable `grid` and then iterating it with a NESTED
`for` makes the parser try to read a grid literal and fail with a message that
names neither the identifier nor the real problem.

## Reproduce

Fails:

```
fn main() -> i64:
    var grid = [[1, 2]]
    for r in grid:
        for c in r:
            print("c={c}")
    0
```

    error: compile failed: parse: Syntax error at 4:9:
    Grid literal must have at least one row

Line 4 is the INNER `for`, which contains no literal at all.

Passes — identical program, variable renamed to `rows`:

```
fn main() -> i64:
    var rows = [[1, 2]]
    for r in rows:
        for c in r:
            print("c={c}")
    0
```

    c=1
    c=2

The only difference is the identifier.

## Second, related spelling failure

The type annotation `[[i64]]` is also claimed by the grid-literal rule and
rejected with the same message:

```
var xs: [[i64]] = []      # Syntax error: Grid literal must have at least one row
```

So a nested list cannot be spelled with its obvious type annotation either.
Seeding from a single-element literal (`var xs = [inner]`) is the only
spelling found that parses.

Note that `[[1, 2]]` as an EXPRESSION does parse — the failure is specific to
the empty-annotation form and to the `grid` identifier, not to nested list
literals in general.

## Why this matters beyond the cosmetic

`grid` is an extremely natural name for 2-D data — layout code, board games,
matrices, terminal cell buffers, the UI scene work. The diagnostic points at
the wrong line and blames a construct the author never wrote, so the cost is
paid in debugging time, not just in a rename.

If `grid` is genuinely reserved, it belongs in the reserved-keyword list in
`.claude/rules/language.md` (currently: `gen`, `val`, `def`, `exists`,
`actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn` — `grid`
is absent). If it is not meant to be reserved, the grid-literal rule needs to
stop firing on a bare identifier in iterable position.

## Workaround in the corpus

`test/fixtures/engine_differential/nested_list_of_lists.spl` renames the
variable to `rows` and documents why, rather than silently normalizing around
it.
