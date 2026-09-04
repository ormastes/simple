# Design — ui_showcase feature screens with button navigation

## Goal

One 2D showcase app that expresses every renderer feature, with menubar
buttons switching screens; each screen exercises a feature group. All four
ScreenHost adapters (2d/gui/web/wm) plus the GPU lanes (Metal, Vulkan) get
the screens for free because content production stays shared in
`showcase_core.spl`.

## Screens (menubar items, index → screen id)

| # | Menu | Screen id | Content |
|---|------|-----------|---------|
| 0 | Overview | `overview` | current layout unchanged: linked scroll pair, free panel, window pair |
| 1 | Fonts | `fonts` | bitmap (5x7) text vs vector (TTF) text, labeled, several sizes |
| 2 | Shapes | `shapes` | alpha rects, edges, polylines (triangle/zigzag/star), clipped+offset group |
| 3 | Scroll | `scroll` | the linked-pair + free panels larger (scroll/clip evidence) |
| 4 | Blend | `blend` | overlapping alpha rects (src-over evidence), opacity ladder |

Every screen keeps the probe panel (last/clicks/drag/typed/input) and
statusbar: event evidence stays visible on all screens.

## Mechanics

- `sc_screen` internal prop on the probe node (same store as `sc_prefix`).
- `_actionable_target` already returns toolbar item ids; the reducer maps
  `{prefix}_toolbar_menu_{i}` → screen id, stores it, and the probe log
  records `screen <id>`. Click counting/focus behavior unchanged.
- Default screen is `overview`; `showcase_build` output is byte-identical to
  before for the default path (spec compatibility).
- Content production: widget tree for widget-expressible content;
  non-widget features (PATH polylines, explicit bitmap/vector text) are
  appended as extra v2 batches via `showcase_composition_extras(prefix,
  screen, w, h, content_rect)`.

## Pipeline changes (minimal, shared)

1. `draw_ir_v2_to_v3.spl`: paint PATH from `cmd.color` (adds PATH to the
   wants-paint set). Today authored v2 paths are transparent everywhere.
2. `scene_raster.spl`: PATH arm — Bresenham lines between consecutive span
   points in the paint fill color, honoring group offset + clip (same walk
   contract as the existing arms).
3. `showcase_core.spl`: `showcase_composition(st, w, h, backend)` =
   widget_tree_to_draw_ir + extras; `showcase_scene` uses it;
   `host_2d_vulkan.spl`'s loop uses it too (one definition).

## Honesty rules

- IMAGE/PORT kinds stay unexpressed: v3 carries a content hash, not pixels;
  the web host fails closed on them by design. The Blend screen's
  "media" slot uses procedural rects (real pixels) instead of faking an image.
- The 2D software raster renders all text as 5x7 bitmap; the Fonts screen
  labels state which lane (bitmap glyph blit vs TTF composite) each line
  exercises on GPU hosts.

## Verification

- Extend `test/03_system/ui_showcase/showcase_hosts_spec.spl` with screen
  switching: click menu index 2 → Shapes scene contains PATH commands and
  the 2D raster paints them (nonzero painted count, distinct pixels).
- Launch matrix: 2D software (scripted nav clicks through all screens,
  per-screen PPM captures), exact Engine2D `software`/`cpu`/`cpu_simd` via
  `hosts/main_2d_engine.spl`, Metal through the same entry with mandatory
  device readback, web (HTML per screen, Chrome screenshots), wm (frame
  bridge), gui (real window). `cpu_simd` must advance the native SIMD hit
  counter; Metal must provide positive backend/device identities. Neither lane
  may accept Engine2D fallback under the requested backend's name.
- Vulkan via MoltenVK on the dev machine.
