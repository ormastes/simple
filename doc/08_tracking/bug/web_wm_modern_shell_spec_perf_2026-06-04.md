# PERF BUG: Web WM modern shell spec exceeds runner perf threshold

Status: open (triaged 2026-06-11)

Observed during focused verification of the Simple Web WM quality/modern shell
contract.

- Date: 2026-06-04
- Command: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean`
- Result: 5 passed, 0 failed
- Duration: 67388ms for `test/01_unit/app/ui/web_wm_modern_shell_spec.spl`
- Runner flag: `[PERF BUG]`

Expected follow-up: split or optimize the broad WM contract spec so focused UI
policy verification can run without crossing the test runner perf threshold.

## Triage 2026-11-25 (P3 ledger lane, Windows host)

Perf half improved, but the spec is now RED — left OPEN, no fix attempted.

Re-ran `SIMPLE_LIB=src bin/simple.exe test test/01_unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean`
(tracked self-hosted binary, two runs): spec-body Duration 37.4s (was 67.4s
in the 2026-06-04 report; no `[PERF BUG]` flag in this run's output), but
`5 examples, 2 failures`:

- `generates rounded translucent WM chrome and motion CSS` — generated page
  no longer contains `<!DOCTYPE html>` as asserted.
- `reports theme quality for color size layout motion and shell affordances` —
  `wm_theme_quality theme=glass_dark status=fail contrast_ratio_x100=998`
  against `expected 998 to be greater than 1700` (contrast gate), plus
  `drag_snap_feedback_ready=false` in the same quality summary.

These are correctness failures in the WM shell generation/quality-contract
code (`app.ui.web.html`, `app.ui.web.wm_quality_contract`), not in the spec's
runtime cost. Splitting/optimizing the spec while it is red would hide real
signal, and changing the assertions is not permitted from this lane; the
contrast/DOCTYPE regressions are WM-feature owner work. The 2026-06-04
"5 passed" evidence above is outdated — current state is 3 passed / 2 failed.
