# GUI Layer Contract — Compositor + Engine2D Locked Surfaces

Status: locked-v1 (2026-04-14)
Owners: os.compositor, lib.common.render_scene, lib.gc_async_mut.gpu.engine2d
Related: `doc/04_architecture/cross_platform_wm.md`, `doc/03_plan/gui_drawing_layer_variations.md`

This document locks the minimal method surface that every compositor
backend, input backend, and 2D-engine backend MUST implement. It is the
work-plan item #1 ("Lock Compositor + Engine2D trait surfaces") from
`gui_drawing_layer_variations.md`. Once merged, any backend that drops
or renames a method here is a breaking change and must update this doc.

## 1. `CompositorBackend` — locked surface

Trait declared in `src/os/compositor/display_backend.spl`. Implemented
by every rendering target (baremetal fb, VirtIO-GPU, winit hosted,
pure-Simple browser buffer, Engine2D wrapper). All colors are packed
u32 ARGB (`0xAARRGGBB`); coordinates are i32 in top-left origin.

| Method | Signature | Semantics |
|---|---|---|
| `width` | `fn width() -> i32` | Backing surface width in pixels. |
| `height` | `fn height() -> i32` | Backing surface height in pixels. |
| `clear` | `me clear(color: u32)` | Fill entire surface with solid color. |
| `fill_rect` | `me fill_rect(x, y, w, h: i32, color: u32)` | Solid-color axis-aligned rect, clipped to surface. |
| `draw_text` | `me draw_text(x, y: i32, text_str: text, fg, bg: u32)` | Paint text at baseline `(x, y)` with fg/bg, 8x16 pitch. |
| `draw_char_8x16` | `me draw_char_8x16(x, y: i32, ch: u8, fg, bg: u32)` | Paint a single VGA 8x16 glyph. Primitive for `draw_text`. |
| `put_pixel` | `me put_pixel(x, y: i32, color: u32)` | Single-pixel write. |
| `present` | `me present()` | Publish current frame (full-surface flip or flush). |
| `present_rect` | `me present_rect(x, y, w, h: i32)` | Publish a rectangular region; may degrade to full present. |
| `read_pixel` | `fn read_pixel(x, y: i32) -> u32` | Sample back-buffer pixel as u32 ARGB. |

### Currently-defined in

| Method | fb | gpu | hosted | browser | engine2d-wrap |
|---|---|---|---|---|---|
| all 10 above | `fb_backend.spl` / `display_backend.spl::FbCompositorBackend` | `display_backend.spl::GpuCompositorBackend` | `hosted_backend.spl::HostedCompositorBackend` | `browser_compositor_backend.spl::BrowserCompositorBackend` | `compositor_engine2d.spl::Engine2dCompositorBackend` |

### Optional subtrait: `CompositorBackendGlass`

Glass/visual-effect methods are split out of the core so backends that
cannot accelerate them (e.g. pure winit) are not forced to stub them.
They currently live on the core trait but should be migrated:

| Method | Signature | Semantics |
|---|---|---|
| `blend_rect` | `me blend_rect(x, y, w, h: i32, color: u32, alpha: u8)` | Alpha-blend a solid rect over existing pixels. |
| `blur_region` | `me blur_region(x, y, w, h: i32, radius: u32)` | Box-blur the region in-place. |
| `gradient_v` | `me gradient_v(x, y, w, h: i32, color1, color2: u32)` | Vertical linear gradient fill. |

Proposed subtrait name: `CompositorGlassCapable`. Widgets must
`if val g = backend.as_glass(): ...` before calling them.

### Optional subtrait: `CompositorBackendResizable`

Not currently on the trait. Needed for hosted/browser backends whose
surface size changes. Proposed:

| Method | Signature |
|---|---|
| `resize` | `me resize(w, h: i32)` |

Recommendation: add as `CompositorResizable` subtrait; baremetal fb/gpu
backends return `nil` from `as_resizable()`.

## 2. `InputBackend` — locked surface

Trait declared in `src/os/compositor/input_backend.spl`. Implemented
by `Ps2InputBackend` (baremetal) and `HostedInputBackend` (winit).
Browser / Electron variations reuse `HostedInputBackend` through winit
event loop or a thin JS bridge.

| Method | Signature | Semantics |
|---|---|---|
| `poll_key` | `me poll_key() -> KeyEvent?` | Non-blocking keyboard poll; `nil` when empty. |
| `poll_mouse` | `me poll_mouse() -> MouseEvent?` | Non-blocking mouse poll; `nil` when empty. |
| `alt_held` | `fn alt_held() -> bool` | Current Alt modifier state. |
| `shift_held` | `fn shift_held() -> bool` | Current Shift modifier state. |
| `ctrl_held` | `fn ctrl_held() -> bool` | Current Ctrl modifier state. |
| `key_to_char` | `fn key_to_char(key: Key) -> text?` | Translate a `Key` enum to its text character given current modifiers. |

### Currently-defined in

| Method | Ps2 | Hosted | Browser/Electron |
|---|---|---|---|
| all 6 above | `input_backend.spl::Ps2InputBackend` | `hosted_input_backend.spl::HostedInputBackend` | (reuses `HostedInputBackend` via winit; no dedicated backend) |

### Optional subtrait: `InputBackendTouch`

Not implemented on any backend today. Proposed future additions:
`poll_touch() -> TouchEvent?`, `poll_gesture() -> GestureEvent?`.

## 3. `Engine2D` — locked surface

Two parallel abstractions exist and must converge:

### 3a. `std.gpu.engine2d.RenderBackend` (GPU/software backends)

Declared in `src/lib/gc_async_mut/gpu/engine2d/backend.spl`.
Implemented by `backend_cpu.CpuBackend`, `backend_software.SoftwareBackend`,
`backend_metal.MetalBackend` (and Vulkan/CUDA/OpenGL variants). The
`Engine2D` facade (`engine.spl`) delegates to an active `RenderBackend`.

| Method | Signature | Semantics |
|---|---|---|
| `name` | `fn name() -> text` | Backend identity ("cpu", "metal", …). |
| `init` | `fn init(w, h: i32) -> bool` | Allocate framebuffer + resources. |
| `shutdown` | `fn shutdown()` | Release resources. |
| `clear` | `me clear(color: u32)` | Fill entire framebuffer. |
| `draw_rect` | `me draw_rect(x, y, w, h: i32, color: u32)` | 1px-stroke rectangle. |
| `draw_rect_filled` | `me draw_rect_filled(x, y, w, h: i32, color: u32)` | Solid rect. |
| `draw_line` | `me draw_line(x1, y1, x2, y2: i32, color: u32, thickness: i32)` | Bresenham line with thickness. |
| `draw_circle` | `me draw_circle(cx, cy, r: i32, color: u32)` | Midpoint circle outline. |
| `draw_circle_filled` | `me draw_circle_filled(cx, cy, r: i32, color: u32)` | Scanline filled circle. |
| `draw_rounded_rect` | `me draw_rounded_rect(x, y, w, h, radius: i32, color: u32)` | Rounded-rect outline. |
| `draw_triangle_filled` | `me draw_triangle_filled(x1, y1, x2, y2, x3, y3: i32, color: u32)` | Filled triangle. |
| `draw_gradient_rect` | `me draw_gradient_rect(x, y, w, h: i32, top_color, bottom_color: u32)` | Vertical gradient rect. |
| `draw_text` | `me draw_text(x, y: i32, text_val: text, color: u32, font_size: i32)` | Text (no bg color). |
| `draw_image` | `me draw_image(x, y, w, h: i32, pixels: [u32])` | Blit an ARGB pixel buffer. |
| `present` | `me present()` | Flush to display. |
| `read_pixels` | `fn read_pixels() -> [u32]` | Read back framebuffer. |
| `width` | `fn width() -> i32` | |
| `height` | `fn height() -> i32` | |

### Currently-defined in

- `backend_cpu.spl::CpuBackend` — reference software path
- `backend_software.spl::SoftwareBackend` — tile-optimized software
- `backend_metal.spl::MetalBackend` — Apple Metal (compute shaders)
- `backend_vulkan.spl`, `backend_opengl.spl`, `backend_cuda.spl` — GPU

### 3b. `common.render_scene.EffectEngine` (int / float precision)

Declared in `src/lib/common/render_scene/engine_trait.spl`. This is the
*effect* engine (per-pixel math), orthogonal to `RenderBackend`. Two
variants:

- `IntEffectEngine` — pure i32/i64, baremetal-safe (no FPU). 8.8 fixed point for filter amounts.
- `FloatEffectEngine` — f64 internally, quality-sensitive.

| Method | Signature |
|---|---|
| `name` | `fn name() -> text` |
| `blend_pixel` | `fn blend_pixel(src, dst: u32) -> u32` |
| `lerp_channel` | `fn lerp_channel(a, b: u32, t_num, t_den: i32) -> u32` |
| `gradient_color` | `fn gradient_color(c1, c2: u32, position, total: i32) -> u32` |
| `shadow_ring_alpha` | `fn shadow_ring_alpha(base_alpha, ring, ring_count: i32) -> i32` |
| `filter_brightness` | `fn filter_brightness(r, g, b: i32, amount: i32) -> [i32]` |
| `filter_contrast` | `fn filter_contrast(channel, amount: i32) -> i32` |
| `filter_grayscale` | `fn filter_grayscale(r, g, b: i32, amount: i32) -> [i32]` |
| `filter_hue_rotate` | `fn filter_hue_rotate(r, g, b, angle_deg: i32) -> [i32]` |
| `filter_sepia` | `fn filter_sepia(r, g, b: i32, amount: i32) -> [i32]` |

### Optional subtrait: `Engine2DExtended`

GPU-only or high-quality-only primitives that software backends may skip:

| Method | Rationale |
|---|---|
| `draw_bezier` | Curves; cpu stubs via line segments. |
| `draw_path` | Generic path; GPU-only. |
| `set_clip(x, y, w, h)` | Scissor rect; cpu backend currently has none. |
| `resize(w, h)` | Framebuffer resize without re-init. |
| `blit_blend(src, dst, alpha)` | Alpha-aware blit. |

Recommendation: create `Engine2DExtended` subtrait, gate GPU-only code
behind `if val ex = backend.as_extended(): ...`.

## 4. Implementation matrix — compositor

Legend: ✅ implemented, ◻ stub (calls fall-through), ❌ missing, — N/A.

### 4a. Compositor backends

| Method | FbCompositorBackend | GpuCompositorBackend | HostedCompositorBackend | BrowserCompositorBackend | Engine2dCompositorBackend |
|---|---|---|---|---|---|
| `width` / `height` | ✅ | ✅ | ✅ | ✅ | ✅ |
| `clear` | ✅ | ✅ | ✅ (`rt_winit_buffer_fill_rect` full) | ✅ (loop) | ✅ (engine.clear) |
| `fill_rect` | ✅ | ✅ | ✅ | ✅ | ✅ |
| `draw_text` | ✅ (driver) | ✅ (per-glyph) | ◻ (via put_pixel) | ✅ | ✅ (rect + overlay) |
| `draw_char_8x16` | ✅ | ✅ | ◻ (glyph via put_pixel) | ✅ | ✅ (1×1 rects) |
| `put_pixel` | ✅ | ✅ | ✅ (1×1 fill_rect) | ✅ | ◻ (1×1 rect) |
| `present` | ✅ (swap) | ✅ (flush) | ✅ | ◻ (no-op; buffer is the output) | ✅ (engine.present) |
| `present_rect` | ◻ (full swap) | ✅ | ◻ (full present) | ◻ | ◻ (full present) |
| `read_pixel` | ✅ (rt_gui) | ✅ (rt_gui) | ❌ | ✅ (buffer index) | ◻ (rt_gui) |
| `blend_rect` (glass) | ✅ (rt_gui) | ✅ (rt_gui) | ✅ (winit_blend) | ❌ | ◻ (rt_gui) |
| `blur_region` (glass) | ✅ (rt_gui) | ✅ (rt_gui) | ✅ (winit_blur) | ❌ | ◻ (rt_gui) |
| `gradient_v` (glass) | ✅ (rt_gui) | ✅ (rt_gui) | ✅ (winit_grad) | ❌ | ✅ (engine) |

Least-complete: **BrowserCompositorBackend** (3 ❌ — no glass) and
**Engine2dCompositorBackend** (4 ◻ — glass leaks through `rt_gui_*`
extern into a non-fb surface, which is a bug on VirtIO-GPU).

### 4b. Input backends

| Method | Ps2InputBackend | HostedInputBackend |
|---|---|---|
| `poll_key` | ✅ | ✅ |
| `poll_mouse` | ✅ | ✅ |
| `alt_held` | ✅ | ✅ (cached from winit) |
| `shift_held` | ✅ | ✅ |
| `ctrl_held` | ✅ | ✅ |
| `key_to_char` | ✅ | ✅ (via helper) |

Both backends are 100% ✅ on the core surface.

### 4c. Engine2D RenderBackend row

| Method | CpuBackend | SoftwareBackend | MetalBackend |
|---|---|---|---|
| `name`, `init`, `shutdown` | ✅ | ✅ | ✅ |
| `clear` | ✅ | ✅ | ✅ |
| `draw_rect` / `draw_rect_filled` | ✅ | ✅ | ✅ |
| `draw_line` | ✅ (Bresenham) | ✅ | ✅ |
| `draw_circle` / `draw_circle_filled` | ✅ | ✅ | ✅ |
| `draw_rounded_rect` | ✅ | ✅ | ✅ |
| `draw_triangle_filled` | ✅ | ✅ | ✅ |
| `draw_gradient_rect` | ✅ | ✅ | ✅ |
| `draw_text` | ✅ (5×7 glyph) | ✅ | ✅ |
| `draw_image` | ✅ | ✅ | ✅ |
| `present` | ✅ (copy out) | ✅ (dirty tiles) | ✅ (GPU flush) |
| `read_pixels` | ✅ | ✅ | ✅ |
| `width` / `height` | ✅ | ✅ | ✅ |

Total cells across compositor matrix: 60. **❌ count: 3**, **◻ count: 9**.
All ❌ and 6 of the 9 ◻ are on BrowserCompositorBackend + Engine2dCompositorBackend.

## 5. Divergences and cleanup items

1. **`fill_rect` edge semantics.** Unspecified today. `FbCompositorBackend`
   passes `(w, h)` through to `FramebufferDriver.fill_rect` which is
   exclusive on the right/bottom edge; `GpuCompositorBackend` uses
   `VirtioGpuDriver.fill_rect` which is also exclusive; the Engine2D path
   follows `draw_rect_filled` which is *inclusive* of `x+w-1, y+h-1`
   (same end pixel, subtly different w,h=0 handling). Recommendation:
   **lock exclusive right/bottom** in this doc, fix `Engine2dCompositorBackend`
   test vectors, and add a conformance test in `wm_compare`.

2. **`present_rect` degradation.** Fb, Hosted, and Engine2D all silently
   degrade `present_rect` to a full present. Only `GpuCompositorBackend`
   actually honors the region. Recommendation: keep the signature, but
   add a capability flag `fn supports_partial_present() -> bool` so
   `Compositor` can skip partial-dirty bookkeeping on backends that
   cannot honor it.

3. **Glass effects bypass the backend.** `FbCompositorBackend`,
   `GpuCompositorBackend`, and `Engine2dCompositorBackend` all call
   `rt_gui_blend_fill` / `rt_gui_box_blur` / `rt_gui_gradient_v` as
   externs targeting the underlying *framebuffer*. When the Engine2D
   backend is actually on VirtIO-GPU or a hosted window, these externs
   paint the wrong surface. `HostedCompositorBackend` correctly routes
   through `rt_winit_buffer_blend_rect` / `_blur_rect`.
   Recommendation: **delete the glass externs from the core trait**,
   move them into the proposed `CompositorGlassCapable` subtrait, and
   make each backend implement them via its own pixel path (no shared
   runtime helper).

4. **`Engine2D.draw_text` drops background color.** The widget layer
   expects `draw_text(x, y, text, fg, bg)` (from `CompositorBackend`)
   but `RenderBackend.draw_text` only takes `color`. `Engine2dCompositorBackend`
   works around it by painting a rect first. Recommendation: add
   `draw_text_bg(x, y, text, fg, bg, font_size)` to the Engine2D
   `Extended` subtrait, keep the one-arg version as the baseline.

5. **No `resize` on any trait.** Hosted and browser backends need it;
   baremetal does not. Must be an optional subtrait, not a core method.

6. **`InputBackend.poll_*` methods vs. `fn` vs. `me`.** The
   `cross_platform_wm.md` spec declares them as `fn`; `Ps2InputBackend`
   implements them as `me`. The `me` form is required because polling
   is stateful (PS/2 buffers advance). Recommendation: lock `me` and
   update `cross_platform_wm.md` in the same PR as this contract.

## 6. Enforcement

- Add a `test/unit/os/compositor/trait_conformance_spec.spl` that
  instantiates every backend as `CompositorBackend` / `InputBackend`
  and calls each method once. Fails to compile if a backend drops a
  method.
- `wm_compare` runs the same scene through all backends and diffs
  pixels. Add a `scene_conformance/` suite that exercises every core
  method in isolation (clear, fill_rect edges, put_pixel at (0,0)
  and (w-1,h-1), present_rect cover, text baseline).

## 7. References

- `src/os/compositor/display_backend.spl` — `CompositorBackend` trait
- `src/os/compositor/input_backend.spl` — `InputBackend` trait
- `src/lib/gc_async_mut/gpu/engine2d/backend.spl` — `RenderBackend` trait
- `src/lib/common/render_scene/engine_trait.spl` — `EffectEngine` trait
- `doc/04_architecture/cross_platform_wm.md` — target architecture
- `doc/03_plan/gui_drawing_layer_variations.md` — work plan
