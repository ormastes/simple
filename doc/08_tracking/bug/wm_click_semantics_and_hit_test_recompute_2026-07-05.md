# WM click semantics fire on down, hit-test recomputed repeatedly without caching

## Status
B1 and B2 landed (commit `0ac3480c8d`, 2026-07-05: "fix(wm): wheel+right/middle
button routing, click-on-release chrome semantics, single hit-test layout per
event, timer deadline clock base"). S3 is **partially** landed by the same
commit — see the 2026-07-11 update below. Line numbers in the sections below
are historical (as of the original report) and no longer match current
`host_compositor_entry.spl` (the close/taskbar dispatch now lives around
:980-1058; :566-577 is now `handle_mouse_wheel`).

## Update (2026-07-11)
- **B1 (fire-on-down) — FIXED.** `host_compositor_left_button_at` in
  `src/os/compositor/host_compositor_entry.spl` (:980-1058) now arms a press
  target (`armed_chrome_target` / `armed_chrome_window_id`) on pointer-down for
  both the close button and taskbar items, and only fires the action on
  pointer-up when the release hit-test still resolves to the same armed
  target (release-inside). A drag-away before release, or a release over a
  different target, cancels the action and clears the armed state
  unconditionally. Covered by `describe "click-on-release chrome semantics
  (FIX 2)"` in
  `test/01_unit/os/compositor/host_compositor_entry_spec.spl`, which now also
  has an explicit "clears the press record after release" scenario proving a
  second independent press/release cycle on a different window is not
  affected by a prior cycle's stale state.
- **B2 (resize-hover minimized guard) — FIXED.** `wm_lifecycle_pointer_move`
  in `src/os/compositor/wm_action_applier.spl:304-313` now gates the
  resize-corner arm check on `not win.minimized`, matching the click hit-test
  and render loop. Covered by `describe "resize-corner hover arming honors
  minimized windows (FIX 2)"` in the same spec file.
- **S3 (hit-test recompute) — PARTIALLY FIXED, remainder still open.** The
  same commit made a single mouse-down event share one `compute_layout()`
  pass across `widget_set_pressed` and `widget_dispatch_click`
  (`src/lib/common/ui/event.spl` `handle_pointer`, `src/lib/common/ui/
  widget_hit.spl`'s `layout` param), cutting a down event from 2 full layout
  passes to 1. Still open: `widget_dispatch_hover` on every mouse-move
  (`event.spl`) still runs its own independent `compute_layout()` with no
  dirty-flag/tree-revision cache, so a move-heavy interaction still pays one
  full layout pass per move event. Left open per this bug's original Next
  Step (layout cache keyed on widget-tree revision + hover short-circuit).

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
