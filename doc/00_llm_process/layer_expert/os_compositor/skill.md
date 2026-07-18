# os.compositor Layer Expert

## Role

Own layer-specific process knowledge for `src/os/compositor/` — the WM
compositor layer: the scene/CSS projection lane (`wm_scene.spl`), the shared
host-compositor bootstrap boundary (`host_compositor_entry.spl`), platform
hosted backends (`hosted_backend_*.spl`), and the shared web-render surface
bridge (`web_render_surface.spl`, `simple_web_window_renderer.spl`).

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)

## Layer Links

- Source: [src/os/compositor/](../../../../src/os/compositor/)
- Scene/CSS lane: `wm_scene.spl` (`standard_wm_scene`, `shared_wm_scene_to_wm_scene`,
  `shared_wm_scene_to_chromed_wm_scene`, `lifecycle_windows_to_motion_wm_scene`,
  `render_scene_to_backend`, `scene_to_html`,
  `WM_SCENE_CSS_RENDER_PIXEL_CAP` = 10000 — above this, the CSS engine is
  skipped for Metal fast-lane or a themed direct-rect fallback).
- Hosted chrome lane: `host_compositor_entry.spl` (`HostCompositor`,
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
  producers `wm_gui_content_frame_from_pixels` / `simple_web_child_content_frame_cached`).

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

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`
