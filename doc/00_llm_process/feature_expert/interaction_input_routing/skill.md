# Interaction / Input Routing Feature Expert

## Role

Own feature-specific process knowledge for the unified, surface-agnostic 2D
interaction core: normalized pointer events, paint-order hit-testing, pointer
capture, and capture/target/bubble dispatch — intended to eventually be
shared by GUI widgets, the browser DOM, and Engine2D/game nodes so paint
order == hit order and every surface dispatches through one contract. Also
covers the half-open hit-test bounds standardization and host/SimpleOS
pointer-input parity work landed alongside it. Phase 1, slice items 2-5 of
the unified 2D engine plan.

## Pipeline Links

- Plan: [doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md](../../../../doc/03_plan/ui/unified_2d_engine/unified_2d_interaction_2026-07-20.md)
  (owner architecture, phases 0-5, Verdict/landing constraints)
- Plan: [doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md](../../../../doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md)
  (phases 0-7, 10-item slice)
- [verify skill](../../../../.claude/skills/verify/SKILL.md)

## Feature Links

- Shared interaction core (new, `e9734f41cf2`):
  [src/lib/common/engine/interaction/](../../../../src/lib/common/engine/interaction/)
  - `mod.spl` — barrel export (`use std.common.engine.interaction.{...}`).
  - `pointer_event.spl` — `PointerEvent2D` (pointer_id/kind/x/y/buttons/
    target/phase + stop/prevent flags), `POINTER_DOWN/UP/MOVE/ENTER/LEAVE/
    OVER/OUT/CANCEL`, `PHASE_NONE/CAPTURE/TARGET/BUBBLE` (all plain `i32`
    codes, not enums — see Gotchas).
  - `hit_proxy.spl` — `HitProxy2D` (half-open AABB + flattened paint-order
    key: stacking_context_order/render_layer/z_index/tree_order/
    insertion_sequence + `pointer_policy`), `paint_key_less` (shared sort
    key so a future renderer sorts identically to hit-testing),
    `POINTER_POLICY_AUTO/NONE/BOUNDING_BOX/PAINTED/FILL/STROKE/SELF_ONLY/
    CHILDREN_ONLY/TRANSLUCENT`.
  - `hit_test.spl` — `hit_stack(proxies, parents, x, y) -> HitTestResult`
    (front-to-back sorted `HitRecord`s), `ancestor_path_of`.
  - `event_route.spl` — `dispatch(event, listeners, ancestor_path) ->
    DispatchOutcome`, `EventListener2D` (node_id/kind/use_capture/once/
    handler), capture -> target -> bubble walk.
  - `pointer_capture.spl` — `PointerRouter` (capture_pointer/
    release_pointer/has_pointer_capture/capture_target, set_hover_path/
    hover_path, set_pressed/clear_pressed/pressed_target),
    `effective_target(router, pointer_id, hit)`, `hover_diff(old_path,
    new_path) -> HoverDiff`.
  - Specs: `interaction_core_spec.spl` (15/15), `probe_interaction_core.spl`
    (38/38), under `test/01_unit/lib/common/engine/interaction/`.
- Half-open bounds convention fix (`ea2e187c394`): browser hit-test in
  [src/lib/gc_async_mut/gpu/browser_engine/layout.spl](../../../../src/lib/gc_async_mut/gpu/browser_engine/layout.spl)
  `_box_contains` changed from inclusive (`<=`) to half-open (`<`) on the
  right/bottom edge, matching `common.ui.widget_hit._contains` and this
  core's `HitProxy2D.contains_point`; `compositor_pick_topmost` /
  `layer_rects_overlap` now exported from `engine2d/__init__.spl` and
  `engine2d/mod.spl`. Spec: `hit_bounds_halfopen_spec.spl` (6/6) + probe
  `probe_hit_bounds_halfopen.spl` (6/6), under
  `test/01_unit/lib/gpu/browser/`. See the
  [browser_engine](../../layer_expert/browser_engine/skill.md) layer
  expert for the layer-owner's note on this fix.
- Host/SimpleOS pointer parity (`09a71feb5c7`):
  - Browser bridge: `translate_mouse_event` in
    [src/app/ui.browser/event_bridge.spl](../../../../src/app/ui.browser/event_bridge.spl)
    now routes middle/right buttons through `UIEvent.MouseEvent(x, y,
    button, kind)` (`mouse_button_name`: 1="middle", 2="right"); left keeps
    the legacy `TouchPress`/`TouchRelease` shape. Spec:
    `test/01_unit/app/ui.browser/input_translation_spec.spl`.
  - PS/2 producer: `_ps2_wm_pointer_button_code` in
    [src/os/compositor/compositor.spl](../../../../src/os/compositor/compositor.spl)
    decodes PS/2 status-byte bits 0/1/2 (left/right/middle) into a shared
    `button_code` (0=none/1=left/2=middle/3=right) and `kind_code`
    (0=none/1=down/2=up/3=move); `prev_wm_pointer_button_code` tracks the
    release edge.
  - SimpleOS decode: `wm_pointer_button_from_code` /
    `wm_pointer_kind_from_code` in
    [src/os/desktop/shell.spl](../../../../src/os/desktop/shell.spl) are
    the consumer side of the same code contract. Spec:
    `test/01_unit/os/desktop/wm_pointer_decode_spec.spl`.
- Related layer experts:
  [browser_engine](../../layer_expert/browser_engine/skill.md),
  [os_compositor](../../layer_expert/os_compositor/skill.md) (neither has
  adopted this core as its dispatch path yet — see Gotchas).

## Gotchas

- **No adapter wiring yet.** This core ships ONLY surface-agnostic
  primitives (Phase 1 slice items 2-5). GUI widgets, the browser DOM, and
  Engine2D/game nodes still use their own ad hoc hit-test/dispatch code —
  slice item 6 (widget/DOM/Node2D adapters) is future work. Do not cite
  this core as "the" pointer-dispatch path for any existing surface until
  an adapter lands.
- **Half-open bounds `[left, right) x [top, bottom)` is now the standard
  convention repo-wide** for anything hit-test-shaped
  (`HitProxy2D.contains_point`, the fixed browser `_box_contains`,
  pre-existing `common.ui.widget_hit`). Default new hit-test code to
  half-open, not inclusive.
- **Event kind/phase are plain `i32` codes, not enum-typed fields** —
  deliberate: an enum-typed struct field with a default has been observed
  left uninitialized by the interpreter on some construction paths (a
  known interpreter landmine). Every construction site in this package
  sets every field explicitly; a future caller relying on a default would
  hit that landmine.
- **`stop_propagation`/`stop_immediate_propagation`/`prevent_default` are
  informational fields only.** `event_route.dispatch()`'s own control flow
  does NOT depend on a listener mutating them via a cross-module `me` call
  mid-loop; listeners instead communicate stop/prevent-default by
  RETURNING an action code (`event_route.ACTION_*`), and `dispatch()`
  writes the final flag state itself (same-function, same-module) before
  returning. They are only safe to read once `dispatch()` has returned.
- **`PointerPolicy` is mostly reserved today.** `hit_test.spl` only
  distinguishes `None` (skip entirely) from everything else — `Auto`/
  `BoundingBox`/`Painted`/`Fill`/`Stroke` all hit-test against the AABB
  identically (there is no rasterized-content/alpha-coverage sampling in
  this core). `SelfOnly`/`ChildrenOnly`/`Translucent` are defined codes
  with NO interpreted behavior yet — reserved for future adapters.
- **PS/2 encode/decode is a producer/consumer pair split across two
  files that must stay in sync:** `compositor.spl`'s
  `_ps2_wm_pointer_button_code` (encode) and `shell.spl`'s
  `wm_pointer_button_from_code` / `wm_pointer_kind_from_code` (decode).
  Codes: button `0=none/1=left/2=middle/3=right`, kind
  `0=none/1=down/2=up/3=move`. Left-button-down values are unchanged from
  the pre-existing contract (backward compatible) — only middle/right and
  up/move are new.
- **Browser mouse translate has two coexisting event shapes**: button 0
  (left) keeps `UIEvent.TouchPress`/`TouchRelease` (no button label);
  middle/right route through `UIEvent.MouseEvent(x, y, button, kind)`.
  Don't assume one variant covers all buttons when consuming
  `event_bridge.spl` output.

## Open Bugs

None filed by this slice (`e9734f41cf2`, `ea2e187c394`, `09a71feb5c7`) — all
three landed with green specs/probes and no new `doc/08_tracking/bug/`
entries.

## Event-backend integration spec (2026-07-21)

`test/02_integration/ui/event_backend_matrix_spec.spl` covers the
backend-integration angle end to end: host `EventBackend` detection
(platform_event, exact-per-OS), EventLoop create/close, ONE composed
hit_stack → dispatch → PointerRouter-capture-redirect scenario (mechanics
depth stays in `interaction_core_spec.spl` — do not duplicate), winit event
type-code drift pins, and UISession keypress smoke. Two interp landmines
force structure choices there:
- `EventLoop.poll` cannot be asserted under ANY sspec `it` (extern's empty
  `[i64]` degrades to i64 0 under the spec runner only) — poll coverage lives
  in the runnable mirror `probe_event_loop_smoke.spl`, following the
  `probe_interaction_core.spl` pattern. Bug:
  `doc/08_tracking/bug/interp_empty_event_array_result_match_erasure_2026-07-21.md`.
- No headless winit/SDL2 availability probe exists yet; only constant pins
  are asserted (SDL2 exposes no named event-type constants at all — gap noted
  in the spec header).

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh
links here BEFORE committing, so the next agent starts from the current
project state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
