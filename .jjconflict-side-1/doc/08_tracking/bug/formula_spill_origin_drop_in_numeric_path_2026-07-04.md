# Formula engine: spill-origin cell contributes wrong value to numeric aggregation over its own spill range

**Date:** 2026-07-04
**Severity:** medium (wrong SUM/AVERAGE results over dynamic-array spill ranges)
**Status:** fixed — see formula_spill_origin_spec.spl

## Symptom

`=SEQUENCE(2,2)` in D1 spills 1..4 into D1:E2, but `=SUM(D1:E2)` returns
**9, not 10** — the origin cell (D1, still a FormulaVal) contributes 0.

## Root cause (exact)

`_resolve_cell_value` (src/app/office/sheets/formula.spl ~L6873-6877, the
numeric/SUM arg path) re-evaluates FormulaVal cells through the SCALAR
evaluation path and **ignores `cached_display`**. Array-returning functions
like SEQUENCE have no scalar handler, so the origin evaluates to 0. By
contrast `_resolve_cell_display_i64` (~L6914) honors cached_display and is
correct.

OFFSET (ref2 batch) masks this for itself because its scalar path returns
the grid's top-left value, which coincides with the spill origin — that is
why `SUM` over an OFFSET spill returns the right total while SEQUENCE does
not. All other array functions (SEQUENCE, MMULT, TEXTSPLIT, SORTBY, …) are
affected when their spill range is aggregated.

## Fix direction

`_resolve_cell_value` should fall back to the cell's `cached_display`
(numeric parse) when scalar re-evaluation of a FormulaVal yields no value /
zero for an array-registered function name — or simply prefer
cached_display for FormulaVal cells whose expression head is in the
`evaluate_formula_array` registry.

## Cross-refs

Found during ref2 review (OFFSET/INDIRECT batch); reviewer-reproduced.
Related: dynamic-array spill design in file_formats.spl two-phase recalc.
