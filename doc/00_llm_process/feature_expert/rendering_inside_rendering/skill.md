# Rendering Inside Rendering Feature Expert

## Role

Own process knowledge for the nested-render-surface capability across the
pure-Simple stack: 2D embedded render targets (offscreen Engine2D composited
into a parent), web-in-web embedding (iframe-like replaced element, private
feature), GUI/WM nested content frames (child `WmContentFrame`s blitted inside
a parent window's content rect), and minimal 3D node nesting. The invariant to
protect: every layer expresses embedding as "render child to an offscreen
`[u32]` surface, composite with position/clip/opacity, fail closed" — no
parallel one-off mechanisms.

## Pipeline Links

- SPipe state: [.spipe/rendering-inside-rendering/state.md](../../../../.spipe/rendering-inside-rendering/state.md)

## Feature Links

- Research (prior art: Chromium viz/OOPIF, Wayland subsurfaces, Godot
  SubViewport `own_world`, Flutter texture layer):
  [doc/01_research/domain/rendering_inside_rendering.md](../../../01_research/domain/rendering_inside_rendering.md)
- Architecture: [doc/04_architecture/ui/rendering_inside_rendering.md](../../../04_architecture/ui/rendering_inside_rendering.md)
- Detail design: [doc/05_design/ui/rendering_inside_rendering.md](../../../05_design/ui/rendering_inside_rendering.md)
- 2D primitive (landed): `Engine2D.create_offscreen` / `draw_engine[_opacity]`
  in [src/lib/gc_async_mut/gpu/engine2d/engine.spl](../../../../src/lib/gc_async_mut/gpu/engine2d/engine.spl);
  Draw-IR embedding realized in
  [src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl](../../../../src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl)
  (`DrawIrEmbeddingConfig.surface_id` → real offscreen composite, depth cap 3,
  full-size/full-opacity perf bypass; `opacity_milli` now honored — unfocused
  WM windows carry 930).
- 2D spec: [test/02_integration/rendering/engine2d_embedded_surface_spec.spl](../../../../test/02_integration/rendering/engine2d_embedded_surface_spec.spl)
- Web embedding (landed): iframe-as-replaced-element in
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  with `space=separate|shared` semantics.
- WM nesting (landed): `WmContentFrame.parent_window_id/offset_*` in
  `src/lib/common/ui/window_scene.spl`, executor recursion in
  `src/lib/common/ui/window_scene_draw_ir.spl`, producers in
  `src/os/compositor/simple_web_window_renderer.spl`.
- Related layer experts:
  [browser_engine](../../layer_expert/browser_engine/skill.md),
  [os_compositor](../../layer_expert/os_compositor/skill.md)
- Adjacent feature expert (verification idiom source):
  [wm_gui_window_drawing](../wm_gui_window_drawing/skill.md)

## Gotchas

- The Draw IR schema already carried embedding metadata
  (`DrawIrEmbeddingConfig`, `DrawIrCommand.parent_id`) long before it was
  honored; check consumers before assuming a schema field is inert.
- Offscreen surfaces must initialize fully transparent (`0x00000000`), not
  opaque black, or parent pixels are wrongly occluded on composite.
- Full-scene batches (e.g. `widget-root`) must bypass the offscreen path or
  every frame pays a redundant full-framebuffer copy.
- Merged interpreter graphs share one enum namespace: the UI `LayoutKind`
  (common/ui/widget_kind.spl) was shadowed by an unrelated compiler enum of
  the same name (`unknown variant or method 'Vbox'`); fixed by renaming the
  compiler enum `TypeLayoutKind` (same class as the Logger collision). When a
  UI spec errors on a variant that plainly exists, grep for same-named types
  in src/compiler/ first. See
  doc/08_tracking/bug/app_ui_render_widgets_html_reexport_gap_2026-07-11.md.

## Session update 2026-07-18

**Glass desktop screendump first-frame heap exhaustion root:** 
`render_baremetal_first_frame` in the SimpleOS desktop-kernel entry creates 
repeated 8MB offscreen render surfaces via `rt_array_repeat` on every frame, 
exhausting heap quickly. The immediate fix is to allocate one embedded software 
surface once and reuse it; this keeps the render surface lifetime consistent 
with the compositor session instead of allocating per-frame.

**Nested WmContentFrame compositing** remains stable; the heap pressure is 
upstream in the first-frame initialization path, not in the embedding/nesting 
machinery itself. See glass-render debugging notes under the rendering layer expert.

**RENDER MILESTONE — offscreen reuse applied:** commit 77acb3e4b8b wires 
`software_backend: sw` in the offscreen constructor, eliminating the per-frame 
allocation storm and enabling stable 99.83% desktop framebuffer coverage 
(3840×2160, 13 colors, zero heap allocations). The invariant holds: nested 
child surfaces (windows, taskbar, embedded app frames) all render to embedded 
offscreen targets and composite into the parent as before; the fix is purely 
at the compositor session level (one persistent software rasterizer per session 
vs per-frame allocation).
