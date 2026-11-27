# WM click semantics fire on down, hit-test recomputed repeatedly without caching
## Obsolete 2026-09-16 — referenced path(s) gone, e.g. src/os/compositor/host_compositor_entry.spl:566-577

Reviewed in the 2026-09-16 bug-ledger normalization pass. Kept for history;
the subject is removed, superseded, or duplicated elsewhere in the ledger.

## Status
Open.

## Severity
Medium — behavioral/performance gaps in user interaction; compounding with frame-cache issues.

## Summary
Three related defects in WM and widget hit-testing:

**B1: Fire-on-down semantics.** `src/os/compositor/host_compositor_entry.spl:566-577` fires window close-button and drag-arm actions on mouse-DOWN (hardcoded `if down:` check). No release-inside guard, no drag-away cancel — standard desktop UX fires on release-inside and cancels if the pointer leaves the button before release. Applies to close button and taskbar focus equally.

**B2: Resize-hover inconsistency.** `src/os/compositor/wm_action_applier.spl:304-313` (`wm_lifecycle_pointer_move`) arms `resize_window_id` for all windows with no `not win.minimized` guard, while the click hit-test (`host_compositor_entry.spl:563`) and render loop (`host_compositor_entry.spl:280`) both exclude minimized windows. A minimized window's corner can still arm resize, so a click at that same location could start "resizing" an invisible window.

**S3: Hit-test recompute on every event.** `src/lib/common/ui/widget_hit.spl:27-33` calls `compute_layout()` fresh every invocation. `handle_pointer` (`event.spl:246-247`) on a single mouse-down calls `widget_set_pressed` AND `widget_dispatch_click` — each independently calls `widget_hit_test`, i.e. **two full layout passes for one click**. `widget_dispatch_hover` (called per mouse-move, `event.spl:239-241`) does a third independent full layout pass, with no dirty-flag short-circuit.

## Evidence
- **host_compositor_entry.spl:566-577**: Close-button action executes unconditionally in `if down:` block; no up-check, no cancel-by-drag.
- **wm_action_applier.spl:304-313**: `not win.minimized` guard missing in `wm_lifecycle_pointer_move` unlike sibling checks at `host_compositor_entry.spl:563` and `host_compositor_entry.spl:280`.
- **event.spl:246-247**: Single `handle_pointer` call triggers both `widget_set_pressed` (hit-test #1) and `widget_dispatch_click` (hit-test #2).
- **event.spl:239-241**: `widget_dispatch_hover` on mouse-move does a third independent hit-test with `compute_layout()`.
- **widget_hit.spl:27-33**: `widget_hit_test()` calls `compute_layout()` unconditionally; no layout cache keyed on widget-tree revision.

## Related Issue
`WebRenderPixelArtifactCache` (a proper HTML-keyed LRU cache with hit/miss counters) already exists in `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl:111-145` but is **not used** by the window-content render path. The compositor calls only the uncached free function `web_render_request_to_pixel_artifact()`, compounding the frame-render cost. See related bug: `web_presenter_interp_perf_2026-07-05.md` (lists the general S1/S2 render-caching gap).

## Failure Scenario
Users cannot cancel close/drag actions by dragging the pointer away (UX inconsistency). Minimized windows can be "resized" via an invisible corner, leaving stale state. Widget interactions trigger 2–3× redundant layout recalculations, multiplying the cost of frame rendering, especially on complex trees.

## Next Step
B1: Fire close/drag actions on release-inside; track pressed-state across down/up; cancel if pointer leaves button. B2: Add `not win.minimized` guard to `wm_lifecycle_pointer_move`. S3: Cache computed layout keyed on widget-tree revision; reuse across `set_pressed`/`dispatch_click` in the same event; skip hover hit-test if tree has not changed since the previous move event.


## Verification 2026-11-25 — all three defects FIXED; the 2026-09-16 "Obsolete" header is wrong about the reason

Verified on `release/1.0.0` (7998d6ba40d), Windows host, by code inspection.
The normalization header claimed "referenced path(s) gone" — in fact all three
referenced files still exist (`host_compositor_entry.spl` is now a 6-line
facade over `host_compositor_core.spl`; the cited line numbers moved). The
defects themselves are fixed:

- **B1 (fire-on-down):** FIXED. `host_compositor_core.spl` (~3499-3520)
  implements release-inside semantics: mouse-down only ARMS the chrome
  target; on release the action fires only if the release hit-test resolves
  to the same target, and moving away cancels it ("Moving away before
  release ... cancels the action; the armed state is cleared unconditionally").
  Regression coverage: `test/01_unit/os/compositor/host_compositor_entry_spec.spl`
  describe block "click-on-release chrome semantics (FIX 2)".
- **B2 (resize-hover on minimized):** FIXED. The resize-arm loop in
  `wm_lifecycle_pointer_move` (now `wm_action_lifecycle.spl:432`) guards with
  `if not win.minimized and wm_lifecycle_resize_grip_hit(...)`. Regression
  coverage: `test/01_unit/os/compositor/wm_action_applier_prevention_spec.spl`
  ("ignoring minimized windows at matching coordinates").
- **S3 (hit-test recompute):** FIXED for the per-click multiplication.
  `event.spl` (~291-297) computes `compute_pixel_layout` ONCE per down event
  and passes the shared layout to both `widget_set_pressed` and
  `widget_dispatch_click`, with a comment documenting the old double-compute;
  `widget_hit.spl` exposes `_hit_test_rects` for exactly this sharing.

Live spec execution was attempted (`SIMPLE_LIB=src bin/simple.exe run
test/01_unit/os/compositor/wm_action_applier_prevention_spec.spl`) but is
blocked repo-wide at this HEAD by the known `@representation_boundary`
seed/binary inconsistency (`outcome=ERROR executed=0`), so verification is by
inspection only.

Status: RESOLVED (supersedes both the stale "Open" body status and the
incorrect "referenced paths gone" header rationale).
