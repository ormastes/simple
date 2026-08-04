# os.compositor Layer Expert

## Role

Own layer-specific process knowledge for `src/os/compositor/` — the WM
compositor layer: the scene/CSS projection lane (`wm_scene.spl`), the host
compositor core (`host_compositor_core.spl` — `class HostCompositor`, WM state,
hit-test, focus, and since 2026-08-04 GUI-session content dispatch), platform
hosted backends (`hosted_backend_*.spl`), and the shared web-render surface
bridge (`web_render_surface.spl`, `simple_web_window_renderer.spl`).

> **Stale-reference warning:** `host_compositor_entry.spl` is now a **6-line
> re-export facade only** (`use os.compositor.host_compositor_core.*` +
> `host_compositor_bootstrap.*`). Any doc citing `host_compositor_entry.spl:NNN`
> for real logic is out of date — the code moved to `host_compositor_core.spl`.
> The production winit entry imports the core directly so optional
> filesystem/background and alternate-backend deps stay out of its native entry
> closure.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)

## Layer Links

- Source: [src/os/compositor/](../../../../src/os/compositor/)
- Scene/CSS lane: `wm_scene.spl` (`standard_wm_scene`, `shared_wm_scene_to_wm_scene`,
  `shared_wm_scene_to_chromed_wm_scene`, `lifecycle_windows_to_motion_wm_scene`,
  `render_scene_to_backend`, `scene_to_html`,
  `WM_SCENE_CSS_RENDER_PIXEL_CAP` = 10000 — above this, the CSS engine is
  skipped for Metal fast-lane or a themed direct-rect fallback).
- Hosted chrome lane: `host_compositor_core.spl` (`HostCompositor` :536,
  `HeadlessHostCompositorBackend`, `HostedWindow`, `render_frame`,
  `host_chrome_scene_html`, `host_chrome_scene_fingerprint`,
  `host_wm_force_direct_chrome` / `host_wm_chrome_force_direct` to pin the
  byte-identical direct-draw fallback for deterministic tests).
- Shared chrome theme (single source of truth for both lanes' colors):
  [src/lib/common/ui/wm_chrome_theme.spl](../../../../src/lib/common/ui/wm_chrome_theme.spl).
- Shared scene projection types: [src/lib/common/ui/window_scene.spl](../../../../src/lib/common/ui/window_scene.spl)
  (`SharedWmScene`, `SharedWmWindow`).
- Taskbar model: [src/lib/common/ui/taskbar_model.spl](../../../../src/lib/common/ui/taskbar_model.spl).
- Unit specs: `test/01_unit/os/compositor/` (e.g. `host_compositor_entry_spec.spl`
  is the reference idiom for constructing `HostCompositor` with a fake/headless
  backend and driving it via `apply_bridge_request`).
- Downstream feature experts depending on this layer:
  [doc/00_llm_process/feature_expert/wm_gui_window_drawing/skill.md](../../feature_expert/wm_gui_window_drawing/skill.md),
  [doc/00_llm_process/feature_expert/rendering_inside_rendering/skill.md](../../feature_expert/rendering_inside_rendering/skill.md)
  (nested `WmContentFrame` compositing: `parent_window_id`/offsets, `WM_CONTENT_ORIGIN_GUI`,
  producers `wm_gui_content_frame_from_pixels` / `simple_web_child_content_frame_cached`),
  [doc/00_llm_process/feature_expert/simpleos_wm_qemu_evidence/skill.md](../../feature_expert/simpleos_wm_qemu_evidence/skill.md)
  (QEMU gate consuming this layer's frames + provenance),
  [doc/00_llm_process/feature_expert/interaction_input_routing/skill.md](../../feature_expert/interaction_input_routing/skill.md).

## Update Rule

When this layer's public contract, source ownership, tests, architecture, or
verification requirements change, update this skill with the new links and
handoff notes.

## Current Frame and Font Ownership (2026-07-14)

- The canonical font-capable frame route is `SharedWmScene ->
  DrawIrComposition -> Engine2D`. `FontRenderBatch` remains transient Engine2D
  material; platform compositor backends present final pixels and must not own
  a private font loader, renderer, atlas, or cache.
- The canonical SimpleOS desktop uses `Engine2dWmFrameExecutor`, and canonical
  ARM64/x86_64 runner/readiness targets select `gui_entry_desktop.spl`. Direct
  legacy `wm_entry.spl` files remain compatibility-only, not production-route
  evidence. Hosted `HostCompositor.render_frame` still ends in the compatibility
  `shared_wm_scene_render_taskbar_context_to_{backend,pixel_buffer}` calls and
  remains pending.
- Route evidence must include the production hosted frame contract and the
  independent SimpleOS QEMU framebuffer crop. Synthetic composition tests and
  serial markers are supporting evidence only.

## Session update 2026-07-18

**OVMF pflash migration (board-runnable rule enforcement):** evidence-gate 
scripts migrating from QEMU `-kernel` to OVMF pflash per board-runnable rule; 
desktop kernel stalls pre-spl_start under OVMF but not `-kernel` (divergence 
open for investigation).

**Glass desktop screendump progress:** first non-black capture (12.64%), fault 
storm reduced 81→1 after NVMe/font fixes; last fault = nil indirect call in 
render_commands (debugging in progress).

### Recent (2026-07-18) Knowledge Links

**OVMF boot resolution (2026-07-18):** pre-spl_start stall was not 
reproducible; boot reaches spl_start identically under OVMF pflash and 
-kernel modes. SimpleOS desktop kernel verified boots under real OVMF pflash 
(not just QEMU `-kernel` pass-through) fulfilling board-runnable rule 
enforcement. See 
`doc/08_tracking/bug/desktop_kernel_ovmf_grub_boot_stall_pre_spl_start_2026-07-18.md`.

**Frame-render path logging:** compositor backends that produce pixel buffers 
should log frame provenance (CPU software paint vs GPU device readback) using 
level-gated probes. See log-retention policy 
[doc/07_guide/infra/logging/log_retention_policy.md](../../../../doc/07_guide/infra/logging/log_retention_policy.md).

## Session update 2026-07-20 (DrawIR incremental patch, host-GPU retention crosslink)

- **DrawIR diff is now O(N), not a nested rescan (`4da2a2b4eb9`):**
  `draw_ir_diff.spl` builds a `DrawIrCommandIndex` (component_id -> flat
  index, first-occurrence-wins on duplicate ids) once per composition
  instead of scanning every batch per lookup; `DrawIrDiffReport` output is
  byte-identical to before (verified). New companion
  [src/lib/common/ui/draw_ir_patch.spl](../../../../src/lib/common/ui/draw_ir_patch.spl)
  is purely additive — it does NOT change `DrawIrCommand`/
  `DrawIrDiffReport` semantics: `draw_ir_patch_between(old, old_rev, new,
  new_rev) -> DrawIrPatch` (insert/remove/update-geometry/update-style/
  update-text/reorder ops + damage rects) and `draw_ir_patch_apply(
  composition, patch) -> DrawIrPatchApplyResult`, revision-gated on
  `composition.composition_id == patch.base_revision` (DrawIrComposition
  has no dedicated revision field by design — `composition_id` doubles as
  the revision key). `draw_ir_patch_commands_equal` is the round-trip
  oracle. Documented, non-silent limitation: only kind/component_id/
  parent_id/geometry/color/text_value/computed_style/glyph_run are
  diffed/compared; glyph-only changes reuse UpdateStyle's full-command carrier —
  border_rect/content_rect/hit_rect/clip_rect/image_uri/edge/points are not
  yet patchable; `apply()` collapses the result into the
  base composition's first batch (multi-batch structural preservation is
  out of scope this slice). Spec: `draw_ir_patch_spec.spl` (13 active;
  current runner execution pending bootstrap repair).
- **`simple test` vs `simple run` divergence on `text?`-lookup + equality
  (bug filed, workaround applied in new code only):** a "loop, return
  first match as `T?`, compare with `== nil`" pattern gives a DIFFERENT
  result under the `simple test` daemon evaluator than under `simple run`
  at ~20-30 element scale (both agree at small scale, which is why this
  went unnoticed for so long). `draw_ir_patch.spl`'s style-compare avoids
  the pattern entirely (raw double-loop membership check, no optional in
  the comparison path); `draw_ir_diff.spl`'s pre-existing
  `_draw_ir_style_changed` carries the SAME latent defect and was
  deliberately left untouched (additive-only constraint on that file's
  report semantics this slice). Filed
  `doc/08_tracking/bug/bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20.md`
  (OPEN). Any new code in this layer doing by-id lookup + equality should
  default to the raw-loop pattern, not `T?` + `== nil`, until this is
  fixed.
- **Host-GPU image-resource retention** (capability-negotiated, wire
  offsets 280/288, fail-closed on an unknown ref) lands in the GPU-offload
  path consumed by
  [src/os/compositor/engine2d_wm_frame_executor.spl](../../../../src/os/compositor/engine2d_wm_frame_executor.spl)
  — full detail lives in the
  [wm_gui_window_drawing](../../feature_expert/wm_gui_window_drawing/skill.md)
  feature expert's 2026-07-20 session update (that gate is the
  consumer/regression check; this layer entry just notes the executor is a
  call site).
- **Not yet wired into this layer:** the new
  [engine_physics](../../feature_expert/engine_physics/skill.md) and
  [interaction_input_routing](../../feature_expert/interaction_input_routing/skill.md)
  feature experts (unified_2d_engine plan Phase 1 slice) ship
  surface-agnostic primitives only — no compositor adapter consumes them
  yet. Don't assume WM pointer dispatch or physics has moved onto the new
  core until an adapter lands here.
  **Partially superseded 2026-08-04:** hosted GUI pointer/key/text dispatch now
  lives in this layer (`HostCompositor.dispatch_gui_*`) — see the 2026-08-04
  session update. It uses `UISession` primitives directly, not the new
  interaction-input-routing core; physics remains unwired.

## Session update 2026-08-04 (HostCompositor owns GUI-session content dispatch)

Landed in `3daf11f4ae` (+237 in `host_compositor_core.spl`, +127 in
`src/os/hosted/hosted_entry.spl`). Closes a P0 gap: a GUI-content window on the
hosted lane rendered but received **no input** — clicks/keys reached WM chrome
only (`grep -c widget src/os/hosted/hosted_entry.spl` was 0, and
`host_gui_event_router.spl` was reachable only from the GLFW demo and 3 specs).

**New HostCompositor state** (`host_compositor_core.spl`):
`gui_content_window_ids` :615, `gui_content_trees` :616,
`gui_content_focused_ids` :617, `gui_pointer_capture_window_id` :618.

**New methods:** `is_gui_content_window` :1121, `attach_window_gui_tree` :1127,
`_release_gui_content` :1151, `dispatch_gui_pointer_event` :1160 (capture on
down / release on up, capture-id rerouting, client-area gate, per-event
UISession rebuild with FocusEvent replay + Resize), `dispatch_gui_scroll_event`
:1218, `dispatch_gui_key_event` :1258 (focus-gated; tab → FocusPrev/Next),
`dispatch_gui_text_event` :1295, `take_gui_content_action` :1318. Cleanup is
wired into `_drop_window_render_state` :723.

**Host/baremetal parity is deliberate.** These mirror the baremetal counterparts
in `src/os/compositor/compositor.spl` — `dispatch_gui_pointer_event` :634,
`dispatch_gui_key_event` :693, `dispatch_gui_text_event` :739, called from
`src/os/desktop/shell.spl:1552`. Hosted client geometry mirrors baremetal too:
`x+4, y+32+extra`, `w-8, h-36-extra`. Routing is **compositor-owned like
baremetal** and uses the same primitives (`UISession.dispatch` /
`dispatch_key_with_modifiers`). `HostGuiEventRouter` was deliberately NOT
duplicated into this path — its GLFW single-window / caller-owned-session
assumptions do not fit winit. Keep future host GUI routing in the compositor,
not in a second router.

**Content-kind gating: `HostedWindow.content_owner`.** `set_external_web_frame`
already sets `HOST_CONTENT_OWNER_GUI` (`wm_action_lifecycle.spl:15`, value 3)
when a frame arrives with `origin_kind == WM_CONTENT_ORIGIN_GUI`;
`attach_window_gui_tree` (:1140) also sets it, so input routes **before the first
frame**. This is the discriminator between the GUI-content lane and the local-web
lane — check it before adding any new content-kind branch.

### Two divergent host WM event lanes (know which one you are in)

- **Production = winit.** `src/os/hosted/hosted_entry.spl`: poll loop :976
  (`rt_winit_event_loop_poll_events`), event-kind constants :153-157
  (EVT_KEY=10, EVT_TEXT=11, EVT_MOUSE_BUTTON=20, EVT_MOUSE_MOVE=21,
  EVT_MOUSE_WHEEL=22), `_host_winit_gui_key_name` :229. GUI branches: mouse-move
  :1019+, mouse-button :1045+ (checked **before** `requires_external_web_frame`,
  because GUI windows also use the external content-frame registry), wheel
  :1373+, key :1442+ (Escape/F11 stay WM-global, matching the browser lane), text
  :1653+. All emit `host_wm_input_record_semantic` receipts with target
  `"gui:session"`.
- **Demo/spec = GLFW.** `examples/06_io/ui/wm_full_stack_demo.spl` +
  `src/os/compositor/host_gui_event_router.spl` (`route_scalar` :118) +
  `src/lib/common/io/window_event.spl` (`WindowEventLoop.poll_scalar` :331).
  **GLFW is not installed on this machine** (no `/opt/homebrew/lib/libglfw*`) and
  `rt_glfw_*` exist only in the native C runtime (`src/runtime/runtime_glfw.c`),
  so this lane is environment-blocked here regardless of code state. Do not treat
  a GLFW-lane spec as evidence for the winit production lane.

For the web/event surface, `hosted_entry` picks a target via
`comp.content_target(...)` / `comp.browser_chrome_target(...)` and dispatches into
`hosted_browser_renderer_registry.spl` + `hosted_web_content_session.spl` — that
lane was already fully wired. The 2D surface remains an **orphaned boundary**:
`src/lib/common/ui/simple2d_gpu_event_boundary.spl` has no `src/**` importer
(only its unit spec); 2D reaches the compositor as PIXELS
(`Engine2dCompositorBackend` → `HostCompositor.render_frame_engine2d`), never as
events.

### Known limits recorded with the change
winit exposes only shift (no ctrl/alt/super externs), so GUI key dispatch passes
shift only; no desktop-clipboard bridging; keycode 122 is both F11 and `z` (F11
wins — pre-existing); releasing a GUI-captured pointer over the browser-profile
window's content routes to the browser branch first.

### Verification reality — specs for this change CANNOT go green here
Spec added: `test/01_unit/os/compositor/host_gui_event_router_spec.spl` (+94, new
describe "hosted compositor GUI-session content dispatch", 3 `it` blocks). It and
`compositor_content_registry_spec.spl` **both fail on this host for a toolchain
reason, not a code reason**: the deployed
`bin/release/aarch64-apple-darwin-macho/simple` (Jul 25) lacks the
`rt_raw_i64_to_string` extern, so every spec importing
`src/lib/common/ui/native_scalar_text.spl` dies with `semantic: unknown extern
function: rt_raw_i64_to_string`
(`doc/08_tracking/bug/deployed_binary_missing_rt_raw_i64_to_string_extern_2026-08-04.md`).
`test/02_integration/ui/event_backend_matrix_spec.spl` is 7 passed / 1 failed for
the same reason. **A stage4 redeploy is what unblocks this** — the stage3
bootstrap binary cannot substitute (it has no `run` command). Nothing in this
section should be read as "verified green".

### Related
- [feature_expert/simpleos_wm_qemu_evidence](../../feature_expert/simpleos_wm_qemu_evidence/skill.md)
  — the QEMU gate that consumes this layer; its current stop is
  `content-provenance-rejected` with an empty `material=`, produced by
  `shared_mdi_framebuffer_scene.spl` / `simple_web_window_renderer.spl` in this
  layer. Documented, not fixed:
  `doc/08_tracking/bug/simpleos_wm_gate_provenance_reject_after_boot_chain_fixes_2026-08-04.md`.
- [feature_expert/interaction_input_routing](../../feature_expert/interaction_input_routing/skill.md)
  — as of 2026-08-04 this layer DOES now own hosted GUI pointer/key dispatch
  (supersedes the 2026-07-20 "not yet wired into this layer" note below for the
  input half; physics is still unwired).
- [feature_expert/wm_gui_window_drawing](../../feature_expert/wm_gui_window_drawing/skill.md)
  — frame/provenance contract on the drawing side.

## Historical Handoff Notes (2026-07-03)

- At that point both WM lanes routed through the shared CSS/GUI-web renderer
  (`std.gc_async_mut.gpu.browser_engine.simple_web_layout_engine2d_fast` /
  `simple_web_html_layout_renderer.spl`, owned by an adjacent browser_engine
  layer, not this one) whenever `engine2d_fast_metal_available()` — that
  renderer is the single point where a CSS parsing/layout regression (e.g.
  the `font:` shorthand weight-as-size bug) affects every WM chrome surface
  at once, in both lanes.
- `wm_scene.scene_to_html()` embeds one large (tens-of-KB, 47+ rule blocks)
  WM chrome stylesheet on every call regardless of scene element count —
  render cost under the interpreter is stylesheet-bound, not pixel-count-
  bound. Budget generous timeouts for anything that calls
  `render_scene_to_backend` at any resolution.
- `HeadlessHostCompositorBackend` is the reusable real pixel-capture backend
  for headless/evidence work against `HostCompositor` (has a genuine
  `pixels: [u32]` field mutated via `put_pixel`/`blit_pixels`); the spec's
  `CaptureCompositorBackend` and `FakeCompositorBackend` are test-only
  (module-global counters, not a readback buffer) and should not be reused
  outside `host_compositor_entry_spec.spl`.

## Theme snapshot access + frame provenance (2026-07-26)

Never consume `active_wm_theme_render_snapshot()` (Option return) on native
lanes — its Some payload masks to null (instruction-proven at
`_wm_draw_ir_window_revision`). Use the owning-module accessors in
`wm_chrome_theme.spl`: `active_wm_theme_id()`,
`active_wm_theme_material_sha256()`, `active_theme_solid_fallback_rgba()`,
or `active_wm_theme_snapshot_present()` + `_unchecked()` for the full
aggregate (bind it to a name other than `snapshot`). The guest WM now
presents frames end-to-end (`content-presented` with 64-char material
digest); its remaining lane gap is app provisioning — `[production-
readiness]` needs 3 spawned app surfaces and `make_os_disk.shs` mode 26
stages no app binaries. Full channel rules:
`doc/07_guide/compiler/backends/freestanding_safe_channels.md`.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
