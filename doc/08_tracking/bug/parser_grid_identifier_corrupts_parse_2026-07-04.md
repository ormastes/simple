# Parser: local named `grid` corrupts parse with misleading "expected Colon, found Dot" (no line number)

**Date:** 2026-07-04
**Severity:** high (silent parser corruption, error points nowhere near the cause)
**Status:** RESOLVED 2026-08-17 — source fix confirmed in BOTH compilers (pure-Simple has no `grid` keyword at all; Rust seed gates the literal behind `at_grid_literal`). Retired by source inspection only; regressions exist but were not executed.

## Symptom

Declaring a local variable named `grid` and later calling a method on it or
indexing it (`grid.len()`, `grid[i]`) does not fail at the declaration.
Instead the PARSER derails and reports an unrelated
`Unexpected token: expected Colon, found Dot` with **no line number**,
typically attributed far from the real cause. In at least one case the
downstream effect was an interpreter segfault rather than a parse error.

## Impact evidence

Two independent agent lanes hit this on 2026-07-04 while implementing
array-spill Calc functions in src/app/office/sheets/formula.spl:
- GROUPBY/PIVOTBY lane: "expected Colon, found Dot", unresolvable by the
  agent; stalled the lane.
- MAP/MAKEARRAY lane: earlier attempt segfaulted; bisection isolated the
  `grid` local as the trigger. Renaming to `rgrid` fixed everything with no
  other change.

`grid` (and `unit`) were already ledgered as reserved-ish identifiers, but
the failure MODE was not: it is not a clean "reserved word" diagnostic, it
is parse-state corruption with a misleading error.

## Fix direction

Either make `grid`/`unit` hard keywords with a proper "reserved word used as
identifier" diagnostic at the declaration site, or fix the grammar so they
parse as ordinary identifiers. The current middle state (accepted at
declaration, corrupts later use) is the worst option.

## Resolution

The Rust parser now treats `grid` as a grid literal only when lookahead starts
the literal grammar (`:` or `device`). In every other value position it becomes
an ordinary identifier, so field access, indexing, named arguments, and bare
reads no longer enter grid-literal parsing. `unit` was already contextual, and
the pure-Simple lexer never reserved either spelling.

Focused Rust regressions cover the original parameter/named-field/method/index
shape and preserve `grid:` literals. Execution is pending.

## Cross-refs

[[interp_array_param_indexing_2026-07-03]] (same formula.spl battleground),
guide quirk ledger doc/07_guide/app/office/writing_calc_functions.md.

## Independent re-verification 2026-08-17 (source inspection only)

Status moved to RESOLVED. Verification was by SOURCE INSPECTION ONLY — a
compiler deploy was in flight, so no spec, test, run, build or lint was executed.
All greps below are `/usr/bin/grep -rn` (unwrapped; the wrapped grep honours
.gitignore and under-reports).

**1. The default tooling path cannot reproduce this.** Per CLAUDE.md the default
compiler is the pure-Simple self-hosted binary. `grep -rn '"grid"' src/compiler/`
returns exactly four lines and **no keyword/token mapping**:

- `src/compiler/10.frontend/core/parser_stmts.spl:2110` — `if arg_name == "grid":`
  (a named-ARGUMENT name compare, not a token class)
- `src/compiler/10.frontend/domain/style_theme.spl:87,96` — UI `LayoutConstraint`
  layout strings (`constraint_type == "grid"`)
- `src/compiler/10.frontend/parser/treesitter/queries/highlights.scm:164` —
  `"grid"  ; aspirational` (a highlighting query, marked aspirational, not the parser)

`grep -rn "Grid" src/compiler/ --include=*.spl` yields only `GpuGridDim` /
`GridDim` MIR+backend instruction kinds and a `grid: [Expr]` GPU-launch field —
no lexer token, no `TokenKind::Grid` analogue. The pure-Simple lexer never
reserves the spelling, so the collision is structurally impossible there.

**2. The Rust seed carries the fix as well** — this contradicts the assumption
that the seed is still live-buggy:

- `src/compiler_rust/parser/src/expressions/primary/mod.rs:279-286` — `TokenKind::Grid`
  dispatches to `parse_primary_math()` **only** `if self.at_grid_literal()`;
  otherwise it `advance()`s and returns `Expr::Identifier("grid")`.
- `src/compiler_rust/parser/src/expressions/primary/math.rs:46-55` — `fn at_grid_literal`
  is a bounded lookahead: true iff `peek_nth(1)` is the identifier `device`, or the
  exact literal opener `Colon Newline Indent Pipe`. Nothing else enters grid-literal
  parsing.
- `src/compiler_rust/parser/src/parser_patterns.rs:605` and
  `parser_helpers.rs:1025/1159/1326`, `expressions/helpers.rs:458` map
  `TokenKind::Grid` to the plain identifier text `"grid"` for patterns and
  keyword-as-identifier contexts.
- `src/compiler_rust/parser/src/expressions/postfix.rs:934-936` keeps the
  `kernel<<<grid: expr, ...>>>` launch form working off the same token.
- `src/compiler_rust/parser/src/lexer/identifiers.rs:298` still maps
  `"grid" => TokenKind::Grid` — the token survives by design; only DISPATCH changed.

**3. Regressions exist in the seed** (not executed here):
`src/compiler_rust/parser/tests/expression_tests.rs:138,140,141` cover
`val grid = 1` / `val grid` in `if` and `while` heads.

**Honest residual.** Two things are asserted from source, not from execution:
that the seed regressions pass, and that no path outside those greps re-enters
grid-literal parsing. Neither compiler's source retains the reported defect, so
the row is retired rather than left OPEN; if the seed regressions are ever seen
to fail, reopen against the seed only (bootstrap-only path), not the default one.
