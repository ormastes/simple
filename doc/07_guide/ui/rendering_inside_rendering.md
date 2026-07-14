# Guide: Rendering Inside Rendering (Embedded Render Surfaces)

How to embed one rendering inside another across the pure-Simple stack.
Architecture: `doc/04_architecture/ui/rendering_inside_rendering.md` ·
Design: `doc/05_design/ui/rendering_inside_rendering.md` ·
Research: `doc/01_research/domain/rendering_inside_rendering.md`

## 2D: offscreen render target

```spl
use std.gpu.engine2d.engine.{Engine2D}

var child = Engine2D.create_offscreen(200, 120)   # CPU backend, transparent
child.clear(0xFF224466u32)
child.draw_rect_filled(10, 10, 60, 40, 0xFFFFFFFFu32)

var parent = Engine2D.create_offscreen(640, 480)
parent.draw_engine(40, 30, child)                  # composite at (40,30)
parent.draw_engine_opacity(300, 30, child, 500)    # 50% opacity
```

Draw-IR path: give a `DrawIrBatch` an embedding with a non-empty
`surface_id` (`draw_ir_embedding_config(surface_id, component_id, x, y, w, h,
layer, opacity_milli, clip)`); the executor
(`engine2d_draw_ir_adv_batch_with_images`) renders that batch into a real
offscreen surface and composites it honoring `opacity_milli`. Empty
`surface_id` keeps the legacy translate+clip behavior. Nesting depth cap: 3.
Note: an embedding at `(0,0)` with full opacity and exactly the target size is
composited 1:1 without an offscreen round-trip (perf bypass).
Resolved IMAGE commands may scale through the canonical Engine2D Vulkan blit
with nearest-neighbor CPU parity. Opaque work uses COPY; transparent work after
opaque initialization uses the same checked shader's src-over mode.

Spec/reference: `test/02_integration/rendering/engine2d_embedded_surface_spec.spl`.

## Web: iframe embedding (private feature)

The production layout renderer (`simple_web_layout_render_html_software_pixels`)
treats `<iframe>` as a replaced element:

```html
<iframe srcdoc="&lt;div style='background:#ff0000;'&gt;child&lt;/div&gt;"
        width="300" height="150" space="separate"></iframe>
```

- Child content comes from `srcdoc` (entity-encoded HTML). `src` is not
  supported in this lane (no filesystem import); fallback children between
  the tags are never rendered.
- Box size: CSS width/height, else `width`/`height` attributes, else 300x150.
- `space="separate"` (default): the child document is styled only by its own
  CSS. `space="shared"`: the parent's CSS rules also apply, child overrides.
- Depth cap 3 (`WEB_IFRAME_DEPTH_CAP`): deeper nesting paints an opaque grey
  placeholder (`0xFF888888`) instead of recursing; a self-embedding page
  cannot recurse unboundedly. Children get half the remaining render budget.

Spec/reference: `test/02_integration/rendering/simple_web_iframe_embedding_spec.spl`.

## GUI/WM: nested content frames

A `WmContentFrame` with a non-empty `parent_window_id` is composited inside
that window's content rect at `(offset_x, offset_y)`, clipped, offsets
accumulating for grandchildren (depth cap 3). Invalid child frames fail
closed (magenta child rect only).

```spl
use common.ui.wm_gui_content_frame.{wm_gui_content_frame_from_pixels}

val child = wm_gui_content_frame_from_pixels(
    "win-1-panel", "win-1", 16, 24, w, h, pixels, scene_rev, content_rev)
# include it in SharedWmRenderInput.content_frames alongside win-1's own frame
```

Web content as a child panel: `simple_web_child_content_frame_cached(...)`
(same renderer as top-level windows, stamped with parent + offset).
Origins accepted: `simple_web`, `gui` (`WM_CONTENT_ORIGIN_GUI`); checksum via
the shared `wm_content_frame_checksum` (63-bit masked).

Spec/reference: `test/02_integration/rendering/wm_nested_content_frame_spec.spl`,
`test/02_integration/rendering/browser_chrome_embedded_rendering_spec.spl`.

## 3D: node-in-node

`Node3.children` holds child nodes whose `center` is RELATIVE to the parent
(positions compose additively; `size` does not compose). Depth cap 8.

```spl
var scene = Scene3(...)
scene.embed("chassis", Node3(name: "wheel", center: vec3(-1.0, -0.5, 0.0), ...))
```

Spec/reference: `test/02_integration/app/model3d/model3d_nested_nodes_spec.spl`.

## Follow-ups (not yet available)

GPU render-to-texture (OpenGL FBO first), input routing/hit-testing into
embedded surfaces, per-iframe JS-runtime space separation.
