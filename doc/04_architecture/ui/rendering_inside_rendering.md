# Architecture: Rendering Inside Rendering (2D / Web / GUI-WM / 3D)

Status: implemented (Lanes A–E landed; GPU render-to-texture and input routing remain follow-ups)
Research: `doc/01_research/domain/rendering_inside_rendering.md`
SPipe state: `.spipe/rendering-inside-rendering/state.md`

## Goal
A uniform nested-render-surface capability across the pure-Simple rendering
stack: 2D embedded render targets, web-in-web embedding (iframe-like, private
feature), GUI panel-in-panel plus web panels inside GUI windows/objects, and
minimal 3D object-in-object nesting — with WM interfaces updated coherently.

## Core decisions
1. **One conceptual RenderSurface pattern, no new cross-layer type.** Every
   layer already reduces content to a flat `[u32]` ARGB buffer
   (`WmContentFrame`, `WebRenderArtifact`, Engine2D `read_pixels`). Nesting is
   therefore realized per layer as: render child into an offscreen `[u32]`
   surface, composite into the parent with position/clip/opacity.
2. **Pixel path and input path are separate concerns** (Flutter texture-layer
   lesson). This arc changes the pixel path; input routing into embedded
   surfaces is a recorded follow-up.
3. **`space: separate | shared` is an attribute of the embedding element**,
   orthogonal to process/thread placement (Chromium agent-cluster and Godot
   SubViewport `own_world` precedent). Separate is the default.
   - No-JS layout renderer: separate = child styled only by its own CSS;
     shared = parent CSS rules also apply (child overrides).
   - JS/session path: separate = own `BrowserRuntimeState`/`JsRuntime`;
     shared = parent runtime handed in.
4. **Depth cap 3 and render-budget sharing** for recursive embedding; beyond
   the cap the renderer degrades (legacy translate+clip in 2D, placeholder
   fill in web) rather than recursing.
5. **Fail-closed compositing.** Invalid child frames render the existing
   magenta failure fill for the child rect only; parents stay intact.
6. **Flat authorities stay flat.** `WindowManager`, `ManagedWindow`,
   `SharedWmScene` keep flat window lists; hierarchy is expressed at the
   content-frame layer (`parent_window_id` + offset) and in Draw IR embedding
   metadata (`DrawIrEmbeddingConfig.surface_id`, `DrawIrCommand.parent_id`).

## Layer designs

### 2D (landed)
- `Engine2D.create_offscreen(w, h)` — CPU/software-backend offscreen target,
  initialized fully transparent so uncovered regions show the parent.
- `Engine2D.draw_engine(x, y, src)` / `draw_engine_opacity(x, y, src,
  opacity_milli)` — compositing primitives built on
  `draw_image_blend(read_pixels())`.
- `draw_ir_adv.spl` honors `DrawIrEmbeddingConfig` for real: a batch with a
  non-empty `surface_id` renders into an offscreen Engine2D and composites at
  `(x, y)` honoring `opacity_milli`; empty `surface_id` keeps the legacy
  translate+clip path exactly. Perf guard: a `(0,0)`, full-opacity,
  target-sized embedding bypasses the offscreen copy (1:1 identical).
- GPU lane: capability-gated `create_offscreen`/render-target extension on
  `RenderBackend` is a follow-up; OpenGL already has FBO SFFI primitives,
  Metal/Vulkan render-to-texture is stubbed.

### Web (Lane B)
- `iframe` handled as a replaced element (like `img`) in
  `simple_web_html_layout_renderer.spl`: children never lay out in the parent,
  box sized by `width`/`height` attrs or CSS (default 300x150).
- Child document from `srcdoc` (primary) or local `src`; painted by a
  recursive call into the same pipeline producing an offscreen `[u32]` buffer,
  blitted at the box origin clipped to the box.
- `space` attribute per decision 3; depth cap 3; child gets a fraction of the
  remaining render budget.

### GUI / WM (Lane C)
- `WmContentFrame` gains `parent_window_id` (empty = top-level) and
  `offset_x/offset_y` relative to the parent's content rect.
- `origin_kind` vocabulary gains `WM_CONTENT_ORIGIN_GUI` alongside
  `simple_web`; frame validation generalizes over registered origins while
  keeping strict revision/checksum/size checks.
- The scene executor (`window_scene_draw_ir.spl`) blits a window's own frame,
  then recursively blits child frames (offsets accumulate, clipped to the
  parent content rect, depth cap 3). `CompositorBackend` is unchanged —
  `blit_pixels` suffices; clipping crops the pixel buffer before the blit.
- Producers: `simple_web_child_content_frame_cached(...)` stamps
  parent/offset on web frames; `wm_gui_content_frame_from_pixels(...)`
  produces GUI-origin frames from raw pixels (same checksum algorithm).
- Draw IR projection mirrors the hierarchy by setting
  `DrawIrEmbeddingConfig.surface_id` and `DrawIrCommand.parent_id` for child
  frames, which the landed 2D executor now composites for real.

### 3D (Lane D, minimal)
- `Node3` gains `children: [Node3]` with child `center` relative to the
  parent; recursive render traversal with depth cap 8; `Scene3.embed(parent
  name, child)` convenience. Engine3d backends untouched (no scene graph
  there today).

## Verification plan
- Per-lane focused specs under `test/02_integration/rendering/` (2D embedded
  surface — landed 5/5; web iframe; WM nested frames) and a model3d spec.
- Final gate: simple web browser chrome check — buttons, GUI elements, text
  fields rendered via the embedding paths with fail-closed pixel evidence,
  following the `scripts/check/check-*-evidence.shs` pattern.

## Follow-ups (recorded, not in this arc)
- Input routing/hit-testing into embedded surfaces (WM surface tree).
- GPU render-to-texture backends (OpenGL FBO first).
- Out-of-process isolation for embedded web instances (excluded by scope).
- Wayland-style sync/desync commit scheduling for child surfaces.
