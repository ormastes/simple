# C-runtime compile gate RED: rt_browser_renderer_namespace_selfcheck.c

Status: OPEN. Filed 2026-08-18.

`sh scripts/check/check-c-runtime-compiles-push.shs` currently reports
`FAIL — 1 file(s) failed to compile: src/runtime/test/rt_browser_renderer_namespace_selfcheck.c (103 compiled clean, 2 skipped...)`.

Timeline evidence: the same gate reported `PASS — 104 file(s) compiled, 0
errors (2 skipped...)` earlier on 2026-08-18 (C-MIG-0013 deletion
verification). The dead-C deletion agent hit the FAIL later the same day and
proved by A/B (change removed → identical failure) that its own deletions are
NOT the cause — the file was broken in between by another session's edit.

Impact: this gate is one of the mandatory pre-push guards, so pushes touching
src/runtime/ will (correctly) block until fixed. Note the file is a TEST
fixture (`src/runtime/test/`), related to `rt_browser_renderer_preinit_active_for_test`
(a cross-TU extern retained as STILL_UNCERTAIN in the dispatch-dead audit).

Wanted: whoever owns the recent browser-renderer edit fixes the fixture; fix
ships with a reproduce check per the Fix test standard
(doc/03_plan/infra/binary_runtime_hardening/plan.md).
