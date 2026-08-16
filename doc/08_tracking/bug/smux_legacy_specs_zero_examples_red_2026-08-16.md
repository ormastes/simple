# smux legacy specs fail the zero-examples gate despite all checks passing

**Date:** 2026-08-16
**Status:** OPEN
**Files:** `test/01_unit/os/smux_spec.spl` (+ identical mirror `test/unit/os/smux_spec.spl`),
`test/01_unit/os/smux/smux_dashboard_spec.spl` (+ mirror `test/unit/os/smux/smux_dashboard_spec.spl`)

## Symptom
`bin/simple test test/01_unit/os/smux_spec.spl` reports
`declared>=1 executed=0 passed=0 failed=1 reason=zero-examples` — permanently RED —
even though the file's own 20 checks all print `PASS` and `DONE`.

## Cause
Both files are legacy main()-style tests (`fn test_*` + `print("PASS: ...")`,
driven by `main()`), not SSpec `describe`/`it` blocks. The runner executes zero
examples and the fail-closed zero-examples gate (correctly) refuses to count a
print-based run as a pass. The print-based checks are also not real oracles — a
`FAIL` print does not fail the process.

## Unblock condition
Convert each `fn test_*` body into an `it` block with `expect`/`assert_*`
oracles (per `.claude/rules/testing.md` Modern SSpec), updating BOTH duplicate
trees identically so `check-test-tree-divergence` stays green. Verified during
the 2026-08-16 smux hardening pass; not converted then because the 2×~400-line
rewrite is independent of that change set.
