# Smux resize content revision exhaustion

Status: OPEN. Source-confirmed at `9ce3db18d9b7c61c80c4aba1447a7969afb0f019`; no executable reproduction or runtime PASS. Independent Astra review was interrupted by its service usage limit.

`PaneRecord.resize` in `src/os/apps/smux/service.spl` increments `content_revision` after `vt_resize` marks capture dirty without checking the u64 ceiling. `resize_layout_children` in `window_layout_service.spl` validates mapping, dimensions and provider support before native resize, but does not reserve content revision capacity. An exhausted participant can therefore reach native effects before its projected revision becomes invalid.

The repair must cover pure planning as well as native dispatch. `apply_window_viewports` resizes records during layout/presentation planning; `resize_pane_plan` directly resizes its original record; `split_checkpoint.spl` restores native dimensions and then resizes records. Checking only the final API configuration revision or only the native loop leaves these paths uncovered. Fresh split records start at revision zero and do not establish capacity for existing participants.

Required behavior:

- Validate every affected existing pane before any grid mutation or native resize. A refused operation preserves geometry, screen, revisions, focus and cleanup authority.
- Preserve no-op behavior at the ceiling when no retained content change is needed; never wrap, reset, reuse or silently saturate an identity.
- Carry attributable errors through pure planners and transactions; do not silently return an unchanged record while committing new geometry.
- Keep native compensation and uncertain-cleanup quarantine intact. Rollback must account for its own revision needs without replacing current output with a stale checkpoint.

Required executable cases: exhausted single pane; exhausted later participant after a writable first pane; pure layout/presentation planning; direct pane resize; split rollback; exact no-op at the ceiling; near-ceiling successful resize and subsequent refusal. Real provider cases must prove no child viewport changed on refusal, retain failure artifacts, and clean up processes. These cases are not yet authored or executed. Resolve this bug before full CoreMux/native qualification.

Partial containment added after discovery: the native transaction's complete validation pass rejects any dimension-changing participant at the u64 ceiling before entering its effect loop. Same-size mappings are not rejected by this revision check. This does not repair earlier pure-plan arithmetic or qualify rollback, and the bug remains OPEN. Source change is uncompiled and unexecuted.

Follow-up source repair: viewport projection now returns a checked Result and admits every participant before resizing any retained grid. All layout, presentation and pane-removal callers propagate that failure. Direct pane planning delegates its sole resize to the checked projection; commit projects before native effects. Exact same-size record resize is a no-op. Split rollback reaches the shared complete native preflight before its record resize. Four explicit-state regression scenarios and their manual are authored, zero executed. Multi-participant, near-ceiling and native rollback evidence remain pending; independent review is unavailable due the Astra usage limit. Status remains OPEN pending that evidence.
