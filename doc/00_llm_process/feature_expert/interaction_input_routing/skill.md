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
- Host WM GUI-content dispatch (`3daf11f4ae`, 2026-08-04) — the production
  winit lane's input path for GUI-session windows; see the dated section
  "Host WM event lanes (2026-08-04)" below for the full contract:
  [src/os/compositor/host_compositor_core.spl](../../../../src/os/compositor/host_compositor_core.spl)
  (`dispatch_gui_pointer_event` :1160, `dispatch_gui_scroll_event` :1218,
  `dispatch_gui_key_event` :1258, `dispatch_gui_text_event`,
  `attach_window_gui_tree` :1127) and
  [src/os/hosted/hosted_entry.spl](../../../../src/os/hosted/hosted_entry.spl)
  (EVT_* branches).
- Related layer experts:
  [browser_engine](../../layer_expert/browser_engine/skill.md),
  [os_compositor](../../layer_expert/os_compositor/skill.md) (neither has
  adopted this core as its dispatch path yet — see Gotchas). Host/QEMU WM
  evidence status:
  [simpleos_wm_qemu_evidence](../simpleos_wm_qemu_evidence/skill.md).

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
- **Two divergent host WM event lanes exist; only one ships.** Production is
  winit (`src/os/hosted/hosted_entry.spl`); the demo/spec lane is GLFW
  (`host_gui_event_router.spl` + `window_event.spl`). Router semantics were
  historically tested only on the GLFW lane, which is not the shipped one —
  and GLFW is not even installed on this machine. Before citing any host
  input behavior as "covered", check WHICH lane the covering spec drives.
  Full detail in the dated section below.
- **Browser mouse translate has two coexisting event shapes**: button 0
  (left) keeps `UIEvent.TouchPress`/`TouchRelease` (no button label);
  middle/right route through `UIEvent.MouseEvent(x, y, button, kind)`.
  Don't assume one variant covers all buttons when consuming
  `event_bridge.spl` output.

## Open Bugs

The original slice (`e9734f41cf2`, `ea2e187c394`, `09a71feb5c7`) filed
nothing — all three landed with green specs/probes. Open as of 2026-08-04,
all blocking VERIFICATION of this area rather than its code:

- `doc/08_tracking/bug/deployed_binary_missing_rt_raw_i64_to_string_extern_2026-08-04.md`
  — the deployed `bin/release/aarch64-apple-darwin-macho/simple` (dated
  Jul 25) has an extern registry without `rt_raw_i64_to_string` (which does
  exist in `src/compiler_rust/common/src/runtime_symbols.rs`). Every spec
  importing `src/lib/common/ui/native_scalar_text.spl` dies with
  `semantic: unknown extern function: rt_raw_i64_to_string`. That is ALL of
  `host_gui_event_router_spec` and `compositor_content_registry_spec`, plus
  1 of 8 in `test/02_integration/ui/event_backend_matrix_spec.spl`.
- `doc/08_tracking/bug/stale_seed_binary_blocks_gpu_web_layout_specs_2026-08-01.md`
  + `doc/08_tracking/bug/parser_trailing_comparison_line_continuation_2026-08-04.md`
  — the same deployed binary predates grammar fix `023a60a05aa`
  (trailing-comparison line continuation), so it cannot parse
  `src/lib/common/web/browser_renderer_protocol.spl` and the entire hosted
  chain was unloadable in the test lane. Worked around by parenthesizing 3
  sites; the binary is still stale.

Unblock for both: a real stage4 deploy. `build/bootstrap/stage3/...simple`
CANNOT substitute — it is bootstrap-only and has no `run` command
(`error: unknown command 'run'`). The rebuild was deliberately deferred by
the user, so **nothing in the 2026-08-04 GUI-dispatch landing below has a
green spec run behind it on this host.** Do not claim otherwise.

## Event-backend integration spec (2026-07-21)

`test/02_integration/ui/event_backend_matrix_spec.spl` covers the
backend-integration angle end to end: host `EventBackend` detection
(platform_event, exact-per-OS), EventLoop create/close, ONE composed
hit_stack → dispatch → PointerRouter-capture-redirect scenario (mechanics
depth stays in `interaction_core_spec.spl` — do not duplicate), winit event
type-code drift pins, and UISession keypress smoke. Notes:
- The EventLoop `it` asserts the FULL smoke including `poll(0)` returning a
  typed empty array — it is the regression gate for the (fixed) interp shim
  that returned `Int(count)` instead of the `[i64]` triple array. The
  runnable mirror `probe_event_loop_smoke.spl` keeps the run/JIT path covered
  (test-path and run-path use different evaluators). Bug history:
  `doc/08_tracking/bug/interp_empty_event_array_result_match_erasure_2026-07-21.md`.
- No headless winit/SDL2 availability probe exists yet; only constant pins
  are asserted (SDL2 exposes no named event-type constants at all — gap noted
  in the spec header).
- **Status 2026-08-04: 7 passed / 1 failed**, and the failure is the stale
  deploy (`rt_raw_i64_to_string`, see Open Bugs), not the code under test.

## Host WM event lanes (2026-08-04)

### The structural finding

There are TWO host WM event lanes, and the one with the router abstraction
is not the one that ships:

- **Production = winit.** [src/os/hosted/hosted_entry.spl](../../../../src/os/hosted/hosted_entry.spl)
  — poll loop at `hosted_entry.spl:960` (`rt_winit_event_loop_poll_events`),
  event-kind constants at `hosted_entry.spl:147-157` (`EVT_KEY=10`,
  `EVT_TEXT=11`, `EVT_MOUSE_BUTTON=20`, `EVT_MOUSE_MOVE=21`,
  `EVT_MOUSE_WHEEL=22`). WM state, dispatch, hit-test and focus all live in
  [src/os/compositor/host_compositor_core.spl](../../../../src/os/compositor/host_compositor_core.spl)
  (`class HostCompositor` :534, `focus_window` :1605, `handle_mouse_button`
  :1755, `handle_mouse_wheel` :1764); `host_compositor_entry.spl` is now
  only a 5-line re-export facade.
- **Demo/spec = GLFW.** `examples/06_io/ui/wm_full_stack_demo.spl` +
  [src/os/compositor/host_gui_event_router.spl](../../../../src/os/compositor/host_gui_event_router.spl)
  (`route_scalar` :118) +
  [src/lib/common/io/window_event.spl](../../../../src/lib/common/io/window_event.spl)
  (`WindowEventLoop.poll_scalar` :331).

`HostGuiEventRouter` was reachable ONLY from the GLFW demo and 3 specs, so
the router's semantics were tested exclusively on the lane that isn't
shipped. GLFW is additionally environment-blocked on this machine: no
`/opt/homebrew/lib/libglfw*`, and `rt_glfw_*` exist only in the native C
runtime (`src/runtime/runtime_glfw.c`).

### P0 fixed: GUI/widget windows were input-dead on the production host WM

`grep -c widget src/os/hosted/hosted_entry.spl` → **0**. A GUI-content
window rendered but received no input at all; clicks and keys reached WM
chrome only. The baremetal compositor already had the counterpart
(`src/os/compositor/compositor.spl` `dispatch_gui_pointer_event` :634,
`dispatch_gui_key_event` :693, `dispatch_gui_text_event` :739, called from
`src/os/desktop/shell.spl:1552`) — the hosted lane simply never grew one.

Landed in `3daf11f4ae`:

- `host_compositor_core.spl` (+237): new fields `gui_content_window_ids`,
  `gui_content_trees`, `gui_content_focused_ids`,
  `gui_pointer_capture_window_id` (`:615-618`); `is_gui_content_window`
  :1121, `attach_window_gui_tree` :1127, `_release_gui_content` :1151,
  `dispatch_gui_pointer_event` :1160 (capture on down / release on up,
  capture-id rerouting, client-area gate, per-event UISession rebuild with
  FocusEvent replay + Resize), `dispatch_gui_scroll_event` :1218,
  `dispatch_gui_key_event` :1258 (focus-gated; tab → FocusPrev/Next),
  `dispatch_gui_text_event`, `take_gui_content_action`. Cleanup is wired
  into `_drop_window_render_state` :731. Hosted client geometry mirrors
  baremetal exactly: `x+4, y+32+extra`, `w-8, h-36-extra`.
- `hosted_entry.spl` (+127): `_host_winit_gui_key_name` :229; GUI branches
  on EVT_MOUSE_MOVE `:1023-1039`, EVT_MOUSE_BUTTON `:1300-1320`,
  capture-release `:1358`, EVT_MOUSE_WHEEL `:1400-1420`, EVT_KEY
  `:1520-1550` (Escape/F11 stay WM-global, matching the browser lane),
  EVT_TEXT `:1697-1712`. Every branch emits a
  `host_wm_input_record_semantic` receipt with target `"gui:session"`.
  **Ordering matters:** the GUI check runs BEFORE
  `requires_external_web_frame`, because GUI windows also use the external
  content-frame registry.

**Content-kind gate.** Routing keys off `HostedWindow.content_owner`.
`set_external_web_frame` already set `HOST_CONTENT_OWNER_GUI` when a frame
arrives with `origin_kind == WM_CONTENT_ORIGIN_GUI`; `attach_window_gui_tree`
now sets it too, so input routes correctly before the first frame ever
lands.

**Why `HostGuiEventRouter` was NOT reused.** It assumes GLFW single-window
and a caller-owned session — neither holds under winit's multi-window,
compositor-owned model. Duplicating it would have re-created the untested
lane. Instead the hosted dispatch calls the same underlying primitives the
router does (`UISession.dispatch` / `dispatch_key_with_modifiers`) with the
compositor owning the session, exactly like baremetal.

Spec added: `test/01_unit/os/compositor/host_gui_event_router_spec.spl`
(+94), new describe "hosted compositor GUI-session content dispatch"
(3 `it` blocks). It cannot run on this host — see Open Bugs.

### Per-surface truth table (host WM)

| surface | events reach the compositor? | entry points |
|---|---|---|
| web | yes, fully wired (pre-existing) | `hosted_entry.spl` picks a target via `comp.content_target(...)` (:1044/:1320) / `comp.browser_chrome_target(...)` (:1045), dispatching into `hosted_browser_renderer_registry.spl` (`dispatch_pointer` :901, `dispatch_scroll` :937, `dispatch_chrome_pointer` :955, `dispatch_key_with_shift` :1019) and `hosted_web_content_session.spl` |
| gui | **yes, as of `3daf11f4ae`** | `HostCompositor.dispatch_gui_*` above |
| 2d | **no — PIXELS ONLY** | `Engine2dCompositorBackend` → `HostCompositor.render_frame_engine2d` |

**The 2D gap is real and is remaining work.** Engine2D reaches the
compositor as a framebuffer and never as events.
`src/lib/common/ui/simple2d_gpu_event_boundary.spl` has NO `src/**` importer
— only its own unit spec. `gpu_web_event_model.spl` / `gpu_event_core.spl`
are likewise a spec-only lane. Their specs are green, which proves the
primitives work, not that anything consumes them. Do not cite 2D input as
wired.

### Known limits of the new GUI lane (recorded, not bugs to re-discover)

- winit exposes only shift (no ctrl/alt/super externs), so GUI key dispatch
  passes **shift only**.
- No desktop-clipboard bridging.
- Keycode 122 is both F11 and `z`; F11 wins. Pre-existing, not introduced
  here.
- Releasing a GUI-captured pointer over the browser-profile window's content
  routes to the browser branch first.

### Where this is verified

Nowhere on this host, honestly. See Open Bugs — the deployed binary's extern
registry blocks the new spec. The related WM gate
`scripts/check/check-wm-browser-event-routing-evidence.shs` also fails closed
at `wm_browser_event_routing_reason=missing-simple-web-font-run-id`
(wrapper line 170, a fail-closed input precondition), because its producer
chain — scenario 1 of
`test/03_system/app/simple_web/feature/web_font_rendering_surface_spec.spl`
→ `build/test-artifacts/simple-web-font-composition/receipt.env` — cannot
compile on the stale binary. On the SimpleOS x86_64 side, QMP input
injection is the branch immediately AFTER readiness, so x86_64 WM input
delivery has still never been proven either — see
[simpleos_wm_qemu_evidence](../simpleos_wm_qemu_evidence/skill.md) and
the [os_compositor](../../layer_expert/os_compositor/skill.md) layer expert.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area, add or refresh
links here BEFORE committing, so the next agent starts from the current
project state.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
