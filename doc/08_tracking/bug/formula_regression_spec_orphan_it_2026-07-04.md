# formula_regression_spec.spl: TREND/GROWTH/PROB/RANDARRAY sections are orphaned `it`s that never ran

**Date:** 2026-07-04
**Severity:** medium
**Status:** source-resolved; regression present, execution pending

## Resolution (2026-07-16)

All five formula sections are now enclosed by `describe` blocks: LINEST,
TREND, GROWTH, PROB, and RANDARRAY contain 28 authored examples in total.
Independently, the runner now executes top-level `it` blocks and fails closed
when authored and recorded example counts differ, so the original silent-skip
condition no longer exists. A fresh executable gate is still pending.

## Original symptom

`test/01_unit/app/office/sheets/formula_regression_spec.spl` had 24
top-level `it` blocks with no enclosing `describe`. Per the test-runner
quirk ("Top-level `it` outside `describe` is silently ignored" — see
`doc/07_guide/app/office/writing_calc_functions.md` quirk-ledger
addendum), none of them ever executed; `bin/simple test` on the file
reported `Passed: 1` (just the file-load check), not 24.

## Original location

`test/01_unit/app/office/sheets/formula_regression_spec.spl` — the
`# LINEST Tests` section was wrapped in `describe "LINEST":` during the
GETPIVOTDATA/AGGREGATE/LINEST/BYROW ceiling-lifting batch (2026-07-04)
because the 2-arg-form-unchanged regression gate for LINEST's new 3-row
stats form depended on it actually running. The `# TREND Tests`, `# GROWTH
Tests`, `# PROB Tests`, and `# RANDARRAY Tests` sections (20 `it` blocks)
are still orphaned and were left alone as out-of-scope for that batch.

## Original fix direction

Wrap each remaining section's `it` blocks in its own `describe` (mirroring
the LINEST section) and re-indent bodies by one level. Re-run the file and
confirm the pass count rises from 7 to ~27 with no regressions (TREND,
GROWTH, PROB, and RANDARRAY all have documented hand-computed/probabilistic
expectations already written — this is purely a structural indent fix, not
new test-writing).
