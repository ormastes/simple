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

## FIXED 2026-08-17 (test-lane)
Both files converted to SSpec: each `fn test_*()` now returns `bool` (the
`print("PASS:")`/`print("FAIL:")` lines became `return true`/`return false`) and
`fn main()` was replaced by a `describe` with one `it` per check
(`expect(test_X()).to_equal(true)`). Both duplicate trees updated by explicit
filename (not glob) and are byte-identical.

Before (`bin/simple test <spec> --no-session-daemon`):
- `test/01_unit/os/smux_spec.spl` — `declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=zero-examples`, exit 1

After:
- `test/01_unit/os/smux_spec.spl` — `declared>=20 executed=20 passed=20 failed=0 dropped=0`, exit 0
- `test/01_unit/os/smux/smux_dashboard_spec.spl` — `declared>=21 executed=21 passed=21 failed=0 dropped=0`, exit 0

Status: FIXED.
