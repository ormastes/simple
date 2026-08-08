# WM: no `pointer_events` / `hit_test` capability for click-through regions

- **Status:** resolved 2026-08-08
- **Found:** 2026-08-07, unit U2.4 of
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`
- **Spec:** `test/03_system/wm/wm_input_routing_system_spec.spl` — it
  `"pointer-events pass through a window region marked non-interactive"`
  (was intentionally RED, now green).

## What's missing

`HostedWindow` (`src/os/compositor/host_compositor_core.spl:320`) has no
field, and `HostGuiEventRouter.update_client_target` /
`update_captured_target` (`src/os/compositor/host_gui_event_router.spl:66-96`)
has no logic, for marking any sub-region of a window as click-through
("`pointer-events: none`" in CSS terms). A probe of
`src/os/compositor/*.spl` for `pointer_events|hit_test` returns zero matches;
the only `pointer-events` string in the repo is CSS text authored by
`src/lib/common/ui/glass_css_surfaces.spl` for in-page styling, which the
compositor's own window-level hit testing never reads.

Consequence: when two windows overlap, the topmost window (last entry to
match in `update_client_target`'s iteration) always wins the whole of its
rect for every routed pointer event -- there is no way for a window to
declare part of itself transparent to clicks so they fall through to the
window underneath.

## Reproduction

`test/03_system/wm/wm_input_routing_system_spec.spl`, it 4: two overlapping
headless-compositor windows A (bottom, created first) and B (top, created
second); a click in their overlap region is routed via two
`HostGuiEventRouter` instances (one per window). The desired end state for a
click-through-marked corner is `routed_to_a == true`, `routed_to_b == false`;
before the fix B unconditionally won, so one of those two assertions failed.

## Resolution

Added a window-local-content-coordinate click-through dead rect and wired it
into hit testing:

- `HostedWindow` (`src/os/compositor/host_compositor_core.spl:320`) gained
  four defaulted fields, `passthrough_x/y/w/h: i32 = 0` (`w == 0` or
  `h == 0` means "no dead region", so every existing construction site is
  unaffected).
- `HostCompositor.set_window_pointer_passthrough(window_id, x, y, w, h)`
  (new `me` method, mirrors the existing `_find_window_index` + mutate
  pattern used by `maximize_window`/`restore_window`) sets the dead rect.
- `HostGuiEventRouter.update_client_target`
  (`src/os/compositor/host_gui_event_router.spl:68`): inside the existing
  per-window content-rect match, if the hit point also falls inside that
  window's declared dead rect, the loop `continue`s instead of claiming the
  match -- so a lower window that already matched keeps its
  `target_window_id`/`last_local_x/y`. `update_captured_target` was
  deliberately left unchanged: an active pointer capture (mid-drag) is
  exclusive by construction and must not be un-captured mid-grab by a
  click-through region meant for ordinary hit-testing; the reason is
  recorded as a comment at the call site.
- **Real defect found and fixed in the same change, not just the new
  capability:** `HostCompositor.pointer_move` -- called on *every* pointer
  move, not just clicks -- round-trips `self.windows` through
  `host_windows_to_lifecycle_state`/`host_windows_from_lifecycle_state`
  (`host_compositor_pointer_move`,
  `src/os/compositor/host_compositor_core.spl:2409`), which does not carry
  `passthrough_*` (same gap `apply_wm_action` already had for
  `maximized`/`restore_*`, worked around there by restoring those fields
  from a pre-action snapshot after the round-trip). Without the same
  restoration in `pointer_move`, the very first mouse-move event after
  `set_window_pointer_passthrough` silently erased the just-set dead rect,
  so the new capability appeared to do nothing end-to-end even though the
  field and hit-test skip were both correct in isolation. Fixed by
  restoring `passthrough_x/y/w/h` from the pre-move snapshot after the
  round-trip, mirroring `apply_wm_action`'s existing pattern.
- The it-4 spec block now calls
  `compositor.set_window_pointer_passthrough(b_id, 0, 0, 152, 124)` (B's
  overlap corner in B-local content coordinates) before asserting
  pass-through, and its docstring/inline comments were rewritten to
  describe the now-real behaviour instead of "expected to stay RED".

## Evidence

Before (baseline, pre-fix):
```
Results: 4 total, 3 passed, 1 failed
```
(it 4: `assert_false failed: got true` -- `routed_to_b` was `true`)

After (post-fix):
```
Results: 4 total, 4 passed, 0 failed
```
via:
```
bin/simple run src/app/test_runner_new/test_runner_single.spl \
  test/03_system/wm/wm_input_routing_system_spec.spl \
  --no-session-daemon --sequential
```

## Not in scope / follow-ups

- `pointer_move`'s lifecycle round-trip (`host_compositor_pointer_move`)
  never restored `maximized`/`restore_*` either -- only `apply_wm_action`
  had that restoration, for a different call path. This fix adds
  restoration of `passthrough_*` in `pointer_move`, matching the immediate
  defect; whether `maximized`/`restore_*` also silently reset on a
  drag-move (as opposed to `apply_wm_action`'s move/maximize/restore
  actions) is a separate, unverified question left for a follow-up probe
  rather than folded into this change.
- `update_captured_target` intentionally does not honor `passthrough_*`
  (see Resolution above); if a future spec needs click-through during an
  active drag/capture, that's a deliberate design decision to revisit, not
  an oversight.
