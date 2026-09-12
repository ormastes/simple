# PERF BUG: Web WM modern shell spec exceeds runner perf threshold

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Observed during focused verification of the Simple Web WM quality/modern shell
contract.

- Date: 2026-06-04
- Command: `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter --clean`
- Result: 5 passed, 0 failed
- Duration: 67388ms for `test/01_unit/app/ui/web_wm_modern_shell_spec.spl`
- Runner flag: `[PERF BUG]`

Expected follow-up: split or optimize the broad WM contract spec so focused UI
policy verification can run without crossing the test runner perf threshold.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
