# UI Browser stage-by-stage logging documented but nonexistent

## Status

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
