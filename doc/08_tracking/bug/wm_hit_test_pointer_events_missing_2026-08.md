# WM: no `pointer_events` / `hit_test` capability for click-through regions

- **Status:** open
- **Found:** 2026-08-07, unit U2.4 of
  `doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md`
- **Spec:** `test/03_system/wm/wm_input_routing_system_spec.spl` — it
  `"pointer-events pass through a window region marked non-interactive"`
  (intentionally RED).

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
today B unconditionally wins, so at least one of those two assertions fails.

## Unblock condition

Add a per-window (or per-region) click-through marker to `HostedWindow` and
have `update_client_target`/`update_captured_target` skip a window whose
matched sub-region is marked non-interactive, falling through to the next
window underneath instead of stopping at the topmost match. The spec's it
block does not yet call any such marker (there is nothing to call) -- it
currently only documents "two overlapping windows, does the click fall
through", which a correct implementation would also fail without the marker
being set. Once the API lands, the it block needs a follow-up edit to
actually mark window B's overlap corner non-interactive before asserting
pass-through; it will not go green from the API change alone.
