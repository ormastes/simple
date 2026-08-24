# Query lint UNUSED001 nested-function scope

Status: open, source-audited, manually unverified.

## Defect

The text fallback treats every deeper line as part of its enclosing function.
A nested local function is therefore included in the outer identifier-frequency
table, while the outer driver's jump to `function_end + 1` prevents a separate
UNUSED001 analysis of the nested function.

## Impact

Names referenced only inside a nested function may suppress outer unused-local
warnings, and unused locals declared inside the nested function may be attributed
to the enclosing scope. Ordinary module functions and sibling class methods are
not affected after the 2026-08-24 indentation-boundary correction.

## Required resolution

Build an indentation-indexed callable scope tree once. Each scope must own only
its direct statements while nested callable intervals are analyzed separately.
Reuse the existing per-scope word table and original-source declaration spans;
do not rescan descendant function bodies for every ancestor. Add nested capture,
shadowing, unused nested local, and multi-level fixtures before enabling the new
scope model.
