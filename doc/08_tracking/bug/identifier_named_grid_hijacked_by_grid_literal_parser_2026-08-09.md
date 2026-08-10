# A local variable named `grid` is hijacked by the grid-literal parser

Status: FIXED 2026-08-09 (see "Root cause and fix" below) — found 2026-08-09 while building
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

## Root cause and fix (2026-08-09)

`grid` is lexed as `TokenKind::Grid` (`parser/src/lexer/identifiers.rs:298`), and
`parse_primary` already tried to keep it *contextual* — but its test was one
token deep:

```rust
let starts_literal = next.kind == TokenKind::Colon
    || matches!(&next.kind, Identifier { name, .. } if name == "device");
```

In `for r in grid:` the token right after `grid` **is** a `Colon` — the `for`
statement's own colon. So the guard fired, `parse_grid_literal` consumed
`: NEWLINE INDENT`, found the nested `for` instead of a `|` row, and reported
"Grid literal must have at least one row" at the inner `for`'s span. Exactly the
same misfire happens for `if grid:` and `while grid:`.

Fix: require the real disambiguating syntax — the row body's leading `|`:

- `src/compiler_rust/parser/src/expressions/primary/math.rs` — new
  `at_grid_literal()`: `grid device=...` (unambiguous) **or**
  `grid : NEWLINE INDENT |`.
- `src/compiler_rust/parser/src/expressions/primary/mod.rs` — the `TokenKind::Grid`
  arm calls `at_grid_literal()` instead of the one-token test.
- `src/compiler_rust/parser/src/parser_helpers.rs` — new `peek_nth(n)`
  (buffered, EOF-clamped) since only `peek_next()` existed.

The pure-Simple parser (`src/compiler/10.frontend`) has no grid-literal rule at
all, so this was contained to the Rust seed. `grid` is **not** reserved and does
not belong in `.claude/rules/language.md`.

### Evidence

Regression tests in `src/compiler_rust/parser/tests/expression_tests.rs`:
`identifier_named_grid_is_not_hijacked_in_iterable_position` (exact bug shape
plus `if grid:` / `while grid:` / assignment / bare use) and
`genuine_grid_literal_still_parses_after_tightened_trigger`.

- RED: with the old one-token trigger restored, the identifier test FAILS
  (34 passed, 1 failed) while the grid-literal test still passes.
- GREEN: with the fix, `cargo test --release -p simple-parser` is fully green
  (276+ across all test binaries, 0 failed).
- End-to-end, the report's exact program: old seed → `Syntax error at 4:9: Grid
  literal must have at least one row`; rebuilt binary → prints `c=1` / `c=2`.

## Second symptom: NOT reproducible, tracked separately

`var xs: [[i64]] = []` parses and runs cleanly on **both** the pre-fix seed and
the fixed binary (rc=0), so the `[[i64]]` annotation failure is not this bug and
was not reproduced in the shape given here. If it resurfaces, capture the exact
surrounding context — it is a type-parser issue, unrelated to `TokenKind::Grid`.

## Workaround in the corpus

`test/fixtures/engine_differential/nested_list_of_lists.spl` renames the
variable to `rows` and documents why, rather than silently normalizing around
it.
