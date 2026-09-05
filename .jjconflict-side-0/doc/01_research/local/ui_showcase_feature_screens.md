# Local research — ui_showcase feature screens (2D GPU hardening)

## What exists today

`src/app/ui_showcase/showcase_core.spl` builds ONE screen: menubar
(["New","Open","Sync","Probe","Quit"], inert until the 2026-08-31 arming fix),
two linked scroll panels, one free scroll panel, two window panels, an event
probe (last/clicks/drag/typed/text-input), statusbar. Four ScreenHost adapters
(2d software raster, gui window, web HTML, wm file bridge) plus
`host_2d_vulkan.spl` (strict Vulkan device receipt) and the Metal path via
`Engine2D.create_with_backend_fast(w, h, "metal")` + the draw_ir_adv executor.

## Renderer feature inventory (DrawIrV3)

Kinds: RECT, TEXT, EDGE, PATH, IMAGE, GROUP, PORT. Flags: CLIPPED,
TRANSFORMED, HIT_TESTABLE, HIDDEN. Paint: fill, stroke, stroke_width_milli,
opacity_milli, blend_mode.

Host coverage (verified 2026-09-01, this tree):

| Feature | 2d raster (scene_raster.spl) | web (host_web.spl) | gui/wm (raster via host) | Metal (draw_ir_adv) | Vulkan (draw_ir_adv strict) |
|---|---|---|---|---|---|
| RECT/EDGE | yes | yes | yes | yes | yes |
| TEXT | yes (5x7 bitmap only) | yes (DOM glyph spans) | yes | yes (5x7 glyph blit + TTF atlas composite) | yes (strict font receipts) |
| GROUP clip+transform | yes | yes | yes | yes | yes |
| PATH | **NO** (silently unpainted) | yes (SVG, line/close verbs) | no | yes (executor arm :2286) | yes |
| IMAGE | no (v3 has content hash only) | no (fail-closed, by design) | no | kind listed; v3 carries no pixels | — |
| PORT | no | no | no | no | — |

Gaps this feature closes:
1. v2→v3 adapter (`draw_ir_v2_to_v3.spl:_v2v3_paint`) never paints PATH —
   `_v2v3_kind_wants_paint` omits it, so authored v2 paths are transparent
   (paint_id = NO_ID) on every host. One-line class fix: paint from
   `cmd.color` like RECT/EDGE.
2. `scene_raster.spl` has no PATH arm — add polyline rasterization
   (Bresenham between consecutive span points, paint fill color) so the 2D
   software host renders every path the web host projects.

## Fonts: bitmap vs vector paths

- Plain v2 text command (no `font-identity` style, no advances): GPU hosts
  take the 5x7 glyph-atlas blit (bitmap font, `common.ui.glyph_bitmap_5x7`).
- Text with `font-identity` + advances (what the widget pipeline emits):
  GPU hosts take the TTF path (FontRenderer → atlas upload → composite).
- 2D software raster: always 5x7 bitmap (`_raster_text_run`), documented.
- Web: DOM spans either way.

The showcase must show both side by side with labels so each lane is
visibly exercised.

## Screen switching

Reducer (`showcase_apply`) already arms+counts menubar clicks
(`_actionable_target`, 2026-09-01). Screen id stored as an internal prop on
the probe node (same pattern as `sc_prefix`). Menubar items become screen
names; the existing spec clicks menu_0 at (20,10) on 160x120, which must
remain actionable (it is — Overview is index 0 and stays the default).

## Host pipeline duality

- v3 hosts (2d/gui/web/wm): `showcase_scene` = v2→v3 of
  `widget_tree_to_draw_ir_cpu(root)` — extras are appended v2 batches before
  conversion.
- GPU hosts (metal/vulkan): `showcase_run_with_backend` /
  `host_2d_vulkan` build the v2 composition directly — the same extras must
  be appended there. Shared helper in showcase_core keeps one definition.

## Backend availability on the dev machine

- Metal: live (rt_metal_* via objc2-metal runtime; seed feature chain added
  2026-09-01).
- Vulkan: MoltenVK present (/opt/homebrew/lib/libvulkan.dylib 1.4.350).
