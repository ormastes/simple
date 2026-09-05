# Chrome ↔ Simple paint-stage I/O contract (stage 5)

This is the third stage of the per-component Chrome↔Simple differential. It is
**not** a whole-page pixel comparison. Each stage fixes an *input* both engines
receive and compares the *output* each engine's own instrumentation reports for
that stage.

| stage | tool | chrome oracle | simple oracle |
|-------|------|---------------|---------------|
| 1–2 DOM + cascade | `tools/web_diff` | `DOMSnapshot.captureSnapshot` computed styles | `parse_html` → `compute_styles` |
| 3–4 layout + text  | `tools/layout_diff` | snapshot `bounds` + `textBoxes` | `layout` box tree + wrap cache |
| **5 paint**        | **`tools/paint_diff`** | **`LayerTree.snapshotCommandLog`** | **`simple_web_layout_render_html_draw_ir`** |

## Why `LayerTree.snapshotCommandLog`

It returns the recorded `SkPicture` for a composited layer — literally the op
stream Blink's paint phase produced, **before** rasterisation. That makes it the
true structural counterpart of Simple's `DrawIrComposition`: both are display
lists, both are produced by the engine itself, and neither has been through a
rasteriser. Comparing them isolates paint defects from raster/AA/font-hinting
noise, which a pixel diff cannot do.

## Input (identical to both engines)

* one fixture from `fixtures/*.html`, loaded from `file://`
* viewport `800×600` css px, `deviceScaleFactor: 1`

## Output (canonical paint-op model)

Both sides are lifted into an ordered list of:

```
{ kind, x, y, w, h, color(u32 AARRGGBB), style, stroke_width?, radius?, text? }
```

### Chrome lift (`chrome_paint_dump.js`)

| Skia command | canonical kind | notes |
|---|---|---|
| `drawPaint` | `canvas_fill` | fills the layer clip |
| `drawRect` styleName=Fill | `fill_rect` | |
| `drawRect` styleName=Stroke | `stroke_rect` | rect is inset by ½ `strokeWidth` |
| `drawRRect` | `fill_rrect` | |
| `drawDRRect` | `stroke_rrect` | rounded border = outer−inner |
| `drawTextBlob` | `text` | `(x, y)` is the **baseline** origin |
| `drawImageRect` | `image` | |
| `clipRect` | `clip_rect` | |
| `save`/`restore`/`concat` | *(dropped)* | structural bookkeeping only |

Coordinates are rounded to integral css px (Simple's DrawIR is `i32`), so a
0.5 px antialias inset never reads as a 1 px divergence. Layer-local coords are
shifted by the layer's `offsetX/offsetY` into document space.

### Simple lift (`simple_paint_dump.spl` + `paint_diff.js`)

`simple_web_layout_render_html_draw_ir(html, w, h)` returns a
`DrawIrComposition` of batches of `DrawIrCommand`. Simple records **one command
per DOM component** carrying the box *plus its computed style*, where Chrome
records **one Skia op per painted primitive**. The differ therefore expands each
Simple component command into the primitives it implies — background fill, then
border stroke, then outline — and marks the derived ones `synthesised: true`.
That expansion is itself a finding (see `border-not-an-op` below).

## Two extractor facts that are load-bearing

Both were established empirically and both fail *silently* — an empty command
log is indistinguishable from perfect agreement:

1. **`--disable-gpu` yields zero layers.** Compositing must be on.
   `--enable-gpu-rasterization` is passed; `--disable-gpu` must not be.
2. **`LayerTree.enable` must be sent once, after a first real paint,** and the
   layer list read off the persistent `LayerTree.layerTreeDidChange` event.
   Enabling before navigation, or cycling enable/disable per fixture, yields
   zero layers.

Because of this, both the extractor and the differ **fail closed**: a fixture
with 0 ops on either side is reported `BLOCKED`, never `PASS`, and the summary
always states the op count compared on *each* side.

## Epsilon

`1` css px on geometry. Colours are compared **exactly** as u32 — a paint-stage
colour is a discrete decision, not a measurement.

## Known modelling caveats

* **Baseline vs top.** Chrome's `drawTextBlob` y is the baseline; Simple's text
  command y is the run top. The differ reports both raw values and the implied
  ascent rather than asserting a conversion.
* **Border insets.** Chrome strokes on the ½-width-inset rect; the differ
  re-inflates to the border box before matching.
* **Occlusion culling.** Chrome drops fully-occluded fills while recording, so
  a Simple fill with no Chrome counterpart is not automatically a defect
  (`18_overflow_clip`). The differ reports both sides' values rather than
  asserting one is wrong.
* **Opacity.** Chrome folds element opacity into the layer/paint alpha; Simple
  carries `opacity` as a style property on the component command. These are
  compared as colours, so an opacity divergence surfaces as `fill-color`.

## Simple text-literal trap

`"body{margin:0}"` written as a Simple text literal parses `{margin:0}` as
string interpolation and fails with ``variable `margin` not found``. Fixtures
are therefore always read from a file, never embedded. Relatedly, a literal
`}}` collapses to a single `}` (the brace escape), which silently emitted
invalid JSON until closes were routed through a `RB` constant.
