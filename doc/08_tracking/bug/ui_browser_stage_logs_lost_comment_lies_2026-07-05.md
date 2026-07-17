# UI Browser stage-by-stage logging documented but nonexistent

## Status
Open.

## Severity
Medium-High — misleading documentation undermines diagnosing known hang bug.

## Summary
`src/app/ui.browser/main.spl:74-77` (comment on real `--open` launch branch) promises "stage-by-stage progress goes to stderr via `app.spl`'s `browser_stage_log` (respects `--quiet`)." Exhaustive grep of `app.spl` and `backend.spl` for `browser_stage_log`, `stage-log`, `args-parsed`, `first-frame-drawn` yields zero matches. Real launch path (`run()` / `run_browser_gui_with_access_store`, lines 150-193, 288-303) contains only 4 hard error messages — no stage instrumentation at all.

## Evidence
- **main.spl:74-77**: Documents stage-logging via `browser_stage_log` function.
- **grep result**: No definition of `browser_stage_log` anywhere in tree (verified 2026-07-05).
- **app.spl real path**: Lines 150-193, 288-303 contain only error messages, no progress instrumentation.

## Failure Scenario
During known CSS-quadratic first-frame hang, operator following documented comment gets zero stderr output and cannot distinguish "still working" from "hung."

## Related Issue (M9 — low confidence, verification-only flag)
`src/os/compositor/hosted_input_backend.spl:171` declares `_has_buffered_mouse: bool`; read as bare field at line 257: `if self._has_buffered_mouse`. This matches the shape of the known `has_*`-prefix field miscompilation (memory: `feedback_has_star_field_bug.md` — bare identifier-receiver reads get miscompiled into method-call lookup and fail at runtime), but every confirmed instance had the field name START with `has_`; here it starts with underscore (`_has_buffered_mouse`). Whether the resolver hijack keys on true prefix or looser pattern is unconfirmed. **Recommended verification**: quick targeted native-build/run smoke test of this class and code path would confirm or rule this out in minutes. Not verified in this read-only sweep.

## Next Step
Either re-add instrumentation via new std.debug stage tracer (P0 module in progress) and fix comment, or remove lying comment. Known issue: stage-logging was added earlier 2026-07-05 but lost (likely parallel-session working-copy clobber). Separately: add M9 smoke test to verify `_has_buffered_mouse` field read behavior.

## Triage note (2026-07-17)

Likely fixed by commit `e6de3effdb5` (2026-07-05): added `std.debug` `dbg_stage` tracer with real stage instrumentation in `app.spl` (parse_start/done, backend_create_start/done, window_created, first_frame_start/done, launch_start, file_checked); `main.spl` comment rewritten to describe the real tracer and cites this bug doc as history. Pending runtime verification of stage instrumentation in live UI launch.
