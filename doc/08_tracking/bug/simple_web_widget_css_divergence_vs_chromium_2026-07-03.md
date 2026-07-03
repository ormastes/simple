# Finding: Simple web engine diverges structurally from Chromium on widget CSS

- **Date:** 2026-07-03
- **Severity:** high for "production level" widget rendering claims
- **Area:** simple web SOFTWARE layout/paint engine (simple_web_html_layout_renderer.spl) — widget CSS features (shadow/gradient/radius/backdrop-blur)
- **Gate:** scripts/check/check-widget-shells-crossengine-evidence.shs (exit 1, status=divergent)

## Measured (same HTML, generate_css("light") widget docs)
| fixture | Simple<->Chrome | Simple<->Electron | Chrome<->Electron |
|---|---|---|---|
| gui window 320x200 | 50.31% | 50.69% | **99.89%** |
| taskbar 480x64 | 47.01% | 47.12% | **99.93%** |
(non-text pixel agreement; per-channel tol <=8, sRGB-normalized, no blur;
glyph pixels excluded via Chrome DOM text mask)

## Finding
The two independent real browsers agree ~99.9% — the HTML/CSS is valid and
consistently rendered. The Simple lane renders a flat fill + single top border
where Chromium renders: border-radius (rounded cards/pill), box-shadow,
linear-gradient backgrounds, accent borders, and nested panel-content boxes.
Panel band top offset 8px (Simple y22 vs Chromium y14).

## Corrected paint-path note (2026-07-03, supersedes earlier draw-ir note)
For THESE fixtures the pixels do NOT flow through the engine2d draw-ir executor
(`draw_ir_adv.spl`). The widget HTML uses class/id `<style>` selectors, so
`simple_web_engine2d_render_html_pixels` routes it to the REAL software layout
renderer: `simple_web_layout_render_html_software_pixels`
(`simple_web_html_layout_renderer.spl`) -> pixels are then uploaded to Metal
purely for readback (`present_layout_pixels_with_engine2d`). So the divergence
lives in the software layout/paint engine, not the draw-ir executor.

The software painter's `Style` DOES parse `border-radius` (per-corner),
`box-shadow` (single, hard offset), and a single `linear-gradient` bg layer.
It has NO radial-gradient, NO shadow blur, NO multi-layer shadow, NO
backdrop-filter. Chromium's widget CSS (`generate_css`) uses ALL of those:
`.widget-panel` = 6-layer soft box-shadow (blur 4..100px, blue glow),
`background: linear-gradient(rgba white..) , #f5f5f5` (translucent overlay),
`border-radius: var(--ui-corner-widget-radius)` (=20px window / 999px taskbar
pill), `backdrop-filter: blur(20px)`; and `body` = three radial-gradients +
a linear-gradient. `var()` custom properties are also not resolved by the
Simple CSS engine, so `border-radius: var(--ui-corner-widget-radius)` yields 0.

## DECISIVE: 80% threshold is unreachable by the flat lane (measured ceiling)
Even a PERFECT flat renderer (exact geometry, white body, white nested panels,
#f5f5f5 outer panel, accent, all pixel-perfect) is bounded by how many of
Chromium's actual pixels fall within per-channel tol 8 of ANY flat color.
Measured on the real captured Chrome ARGB:

| fixture | flat ceiling (6-colour palette, tol8) | strict (white/#f5f5f5/accent) | threshold |
|---|---|---|---|
| window 320x200 | **63.4%** | 54.0% | 80% |
| taskbar 480x64 | **69.7%** | 56.9% | 80% |

Verified through the gate's OWN comparator (compare-widget-crossengine.js):
feeding it a synthetic "ideal flat" Simple bitmap built by snapping every
captured Chrome pixel to its nearest theme color (white/#f5f5f5/accent) — i.e.
the absolute upper bound of any flat renderer with perfect color placement —
yields simple<->chrome non-text agreement of **54.00%** (window) / **56.93%**
(taskbar). That is the true ceiling for the flat lane; both are far below the
80% pass threshold, so NO flat-lane code change (geometry, radius, hard borders,
flat panels) can flip this gate.

~31–37% of Chrome's pixels are intermediate shadow/gradient/AA tones (grays
200–240 + bluish 232,232,240 body-gradient tints, a smooth continuum no small
palette covers). Reaching 80% therefore REQUIRES reproducing Chromium's soft
multi-layer box-shadows, radial + linear gradients, translucent gradient fills,
and backdrop-blur to per-channel tol 8 — a browser-compositor-scale effort the
current flat engine2d/software lane cannot do (no blur, no radial-gradient
primitive). This is exactly the "soft shadows" residual the gate design
anticipates. The comparator/thresholds were NOT loosened.

## Secondary (real) layout bugs, independent of the shadow ceiling
- Panel band top offset 8px: Simple y22 vs Chromium y14 (both fixtures).
- Window panel stretches full height (Simple bottom y199) vs Chromium
  content-height (y167, delta 32px) — Simple stretches the flex root to the
  viewport instead of sizing to (empty) content.
Fixing these would make the binary panel-band match true but still cannot flip
the gate while non-text agreement is ceiling-bound below 80%.

## Fixture had been deleted from the tree; restored
`src/app/wm_compare/production_gui_window_taskbar_widget_shells.spl` was absent
from HEAD (removed in adfcb2ba45; last full version in f37d7d8764). The gate
driver hard-references it, so it was restored from f37d7d8764 (218 lines) to let
the gate render real evidence instead of failing to resolve the module.

## Empty text mask (render_html_tree drops children)
`render_html_tree` emits the nested `.widget-panel`/`.panel-content` boxes but
NOT their label/button children, so the Chrome DOM geometry yields 0 text rects
and the comparator compares the WHOLE frame as non-text. This does not affect
the ceiling conclusion (text is a tiny fraction here) but is why
`*_text_mask_rects=0`.

## Artifacts
build/widget_shells_crossengine/{simple,chrome,electron}_{window,taskbar}.png
+ report.md (2026-07-03 run). Ceiling script:
scratchpad/ceiling.js (flat-palette agreement bound on the captured Chrome ARGB).

## Also noted (pre-existing runtime gaps, not worked around silently)
- rt_string_builder_new extern unavailable in current self-hosted runtime
  (array-backed StringBuilder fallback used).
- Reading a binary PNG via std.io_runtime.file_read crashes the interpreter
  on rt_dir_exists.
