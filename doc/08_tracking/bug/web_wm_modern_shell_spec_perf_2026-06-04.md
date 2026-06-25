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
