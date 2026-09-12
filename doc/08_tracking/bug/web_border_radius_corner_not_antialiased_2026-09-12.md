# border-radius corners are not anti-aliased (2026-09-12)

**Status:** PARTIALLY FIXED. Framebuffer painter fixed; **Engine2D painter
reverted and BLOCKED** — see "Why the Engine2D half was reverted".
**Component:** pure-Simple web renderer paint primitives; Engine2D emulation
backend.

## Defect

Both rounded-corner rasterizers used a hard in/out membership test, so a corner
stepped straight from fill to background with no intermediate value anywhere.
Chrome ramps 234→233→229→223→255 across the same arc. On a 160x160 fixture with
a 100x100 black box at (20,20) and `border-radius:40px`, Simple produced exactly
**2 distinct colours** over 25,600 px.

- Framebuffer painter:
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl`,
  `fb_rounded_rect_corners_opacity_clip` — `inside = dx*dx + dy*dy <= r*r`.
- Engine2D painter: `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`,
  `_emu_corner_arc` — a midpoint-circle span fill. This is the painter the
  cpu_simd web lane actually reaches (`backend_software.spl:547` delegates
  `draw_rounded_rect` to `emu_draw_rounded_rect`).

`simple_web_css_box_effects.spl:82` parses the radius correctly; the defect is
in the painters.

## Fix (framebuffer painter — landed)

Replaced the boolean with an analytic coverage in 0..256:
`cov = clamp(r*256 + 128 - dist256, 0, 256)`, where `dist256` is an integer
Newton square root of the squared distance in 1/256-px units. The ramp is one
pixel wide and crosses 1/2 exactly on the arc; the tangent row/column keeps full
coverage, so no half-coverage notch appears on the straight edges. New helpers
`_isqrt_i64`, `_corner_coverage256`, `_blend_alpha256` in the same file.

## Why the Engine2D half was reverted

The analytic-coverage version of `emu_draw_rounded_rect` was written and
**verified to work** — the same fixture rendered 23 distinct colours instead of
2, with a correct ramp along the whole arc (measured values 230/179/134/96/64/38/19/6
across one row).

It was reverted because
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` pins the
CPU fill against an independent Simple replica of the GPU
`kernel_draw_rounded_rect` **band/corner membership formula** — an explicit
CPU↔GPU parity contract (see that file's comment at :822-830). The change took
it from 1 pre-existing failure to 5:

```
✗ matches the band/corner formula on the original bug-doc fixture (radius=6, ...)
✗ matches the band/corner formula when radius == min(w,h)/2 (stadium shape)
✗ matches the band/corner formula on a narrow strip (h < 2*radius ...)
✗ matches the band/corner-fill+blend formula on a semi-transparent fill ...
```

Those oracles are not stale — they assert cross-backend agreement. Landing
corner AA on the CPU alone would make the CPU disagree with the Metal and Vulkan
kernels. The unblock condition is a **coordinated shared-raster change**: the
analytic coverage formula must land in `kernel_draw_rounded_rect` (Metal MSL and
Vulkan) and in the parity spec's replica in the same change. Those backends were
owned by another lane at the time of this fix, so it is filed rather than forced.

## Specs

- `test/unit/browser_engine/border_radius_antialias_spec.spl` — GREEN.
  Calls `fb_rounded_rect_corners_opacity_clip` directly on a 40x40 buffer:
  exact fill well inside the arc, untouched background at the corner tip, and at
  least 8 pixels in the corner tile that are neither (a hard in/out test produces
  exactly zero).
- `test/unit/browser_engine/border_radius_antialias_engine2d_spec.spl` — **RED,
  `# @tag:in-development`.** Renders the HTML fixture through the cpu_simd lane
  and asserts an intermediate value on the arc at (31,31) and (53,20), exact fill
  at (60,60), exact background at (21,21), and no notch on the tangent edges.
  Currently 1 of 3 examples fails — exactly the AA assertion. Per
  `.claude/rules/testing.md` this is left RED rather than weakened.

Both mirrored into `test/01_unit/browser_engine/`.
