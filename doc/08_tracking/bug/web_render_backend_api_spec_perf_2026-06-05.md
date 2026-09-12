# PERF BUG: Web render backend API spec exceeds runner perf threshold

Status: open (triaged 2026-06-11)

Observed during focused verification for the shared GUI web renderer parity
work.

- Date: 2026-06-05
- Command: `bin/simple test test/01_unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter`
- Result: 11 passed, 0 failed
- Duration: 71354ms for `test/01_unit/app/ui/web_render_backend_api_spec.spl`
- Runner flag: `[PERF BUG]`

Expected follow-up: split or optimize the broad backend API contract spec so
focused UI adapter verification can run without crossing the test runner perf
threshold.

## Triage 2026-09-12

Re-verified 2026-09-12: still reproduces — `bin/simple test test/01_unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter` still exceeds a 150s budget (had to be run in the background past the 120s foreground cap) on deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59); spec now has 19 examples (18 passed, 1 unrelated GPU-permission failure) vs the 11 examples cited when filed. Status kept as OPEN.
