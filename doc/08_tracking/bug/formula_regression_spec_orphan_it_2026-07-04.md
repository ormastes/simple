# formula_regression_spec.spl: TREND/GROWTH/PROB/RANDARRAY sections are orphaned `it`s that never ran
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-04
**Severity:** medium
**Status:** open

## Symptom

`test/01_unit/app/office/sheets/formula_regression_spec.spl` had 24
top-level `it` blocks with no enclosing `describe`. Per the test-runner
quirk ("Top-level `it` outside `describe` is silently ignored" — see
`doc/07_guide/app/office/writing_calc_functions.md` quirk-ledger
addendum), none of them ever executed; `bin/simple test` on the file
reported `Passed: 1` (just the file-load check), not 24.

## Where

`test/01_unit/app/office/sheets/formula_regression_spec.spl` — the
`# LINEST Tests` section was wrapped in `describe "LINEST":` during the
GETPIVOTDATA/AGGREGATE/LINEST/BYROW ceiling-lifting batch (2026-07-04)
because the 2-arg-form-unchanged regression gate for LINEST's new 3-row
stats form depended on it actually running. The `# TREND Tests`, `# GROWTH
Tests`, `# PROB Tests`, and `# RANDARRAY Tests` sections (20 `it` blocks)
are still orphaned and were left alone as out-of-scope for that batch.

## Fix

Wrap each remaining section's `it` blocks in its own `describe` (mirroring
the LINEST section) and re-indent bodies by one level. Re-run the file and
confirm the pass count rises from 7 to ~27 with no regressions (TREND,
GROWTH, PROB, and RANDARRAY all have documented hand-computed/probabilistic
expectations already written — this is purely a structural indent fix, not
new test-writing).

## Addendum 2026-11-11 — lane runner4: SUPERSEDED

All five sections (LINEST, TREND, GROWTH, PROB, RANDARRAY) are now wrapped
in `describe` blocks at `test/01_unit/app/office/sheets/formula_regression_spec.spl:114,207,254,310,377`.
Fix is in the ancestry of release/1.0.0 tip `b364745fdbf8` (file last
changed by merge `9e7e7a526edb`, PR #7597, 2026-11-07). Note the in-file
comment at lines 104-111 claiming TREND/GROWTH/PROB/RANDARRAY are "still
orphaned" is now stale — the wrapping landed with the file at this tip.

seed-smoke verification (refreshed seed 2026-11-11,
`SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test
test/01_unit/app/office/sheets/formula_regression_spec.spl
--mode=interpreter --no-cache`):

```
SPEC FILE VERDICT: ... outcome=OK declared>=28 executed=28 passed=28 failed=0 skipped=0 dropped=0
Results: 28 total, 28 passed, 0 failed
```

28/28 executed and passed (expected rise "7 to ~27" met and slightly
exceeded — 28 `it` blocks). No regressions. Verdict: SUPERSEDED.

