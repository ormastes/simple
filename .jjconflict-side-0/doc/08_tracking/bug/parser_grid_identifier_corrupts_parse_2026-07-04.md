# Parser: local named `grid` corrupts parse with misleading "expected Colon, found Dot" (no line number)

**Date:** 2026-07-04
**Severity:** high (silent parser corruption, error points nowhere near the cause)
**Status:** source fixed in Rust parser 2026-07-15; focused execution pending

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
