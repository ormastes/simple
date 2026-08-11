# tools/paint_diff — Chrome ↔ Simple paint-stage differential

Stage 5 of the per-component Chrome↔Simple renderer differential: compare the
**display list** each engine records for the same HTML fixture.

* Chrome's output: `LayerTree.snapshotCommandLog` — the layer's recorded
  `SkPicture` op stream, i.e. what Blink's paint phase emitted, before raster.
* Simple's output: `simple_web_layout_render_html_draw_ir` →
  `DrawIrComposition` — Simple's own display list.

This is an **input/output** comparison per rendering component, not a whole-page
pixel comparison. See `CONTRACT.md` for the canonical op model, the lift tables,
and the epsilon.

## Run

```sh
sh tools/paint_diff/run_paint_diff.shs
# or point at a specific browser
sh tools/paint_diff/run_paint_diff.shs --chrome /path/to/chrome
```

Outputs (all gitignored):

```
out/chrome/<fixture>.chrome.json   normalised Skia op stream per layer
out/simple/<fixture>.simple.json   DrawIrComposition, paint-relevant style slice
out/paint_report.json              findings, with BOTH engines' values
```

Exit codes: `0` compared successfully (findings are data, not failure),
`2` nothing was compared, `4` no chrome executable found.

## Fail-closed design

An empty command log looks exactly like perfect agreement, and two of the CDP
ordering requirements fail silently (see CONTRACT.md). So:

* the extractor exits non-zero if Chrome yields 0 ops overall;
* a fixture with 0 ops on either side is reported **BLOCKED**, never PASS;
* the summary always prints the op count compared on *each* side;
* every finding states **both** Chrome's value and Simple's value — a bare
  "Simple differs" is not a finding.

## Measured baseline (Chrome for Testing 151.0.7922.34, 800×600)

18 fixtures, **68 Chrome paint ops** vs **88 Simple paint ops**
(fill 38 / 38, stroke 2 / 3, text 7 / 7), **16 divergences**.
10 fixtures match exactly: `01_solid_fill`, `02_two_fills`, `05_padding_fill`,
`06_nested_fills`, `07_text_color`, `09_border_radius`, `11_overlap_zindex`,
`12_transparent_bg`, `13_rgba_alpha`, `17_multi_text_lines`.

| # | fixture | Chrome | Simple |
|---|---------|--------|--------|
| 1 | `03_border_solid` | `drawRect style=Stroke width=4 colour=#FF008000` — a border is **its own paint op** | no border command at all; `border-*-width={t:4,r:4,b:4,l:4}` colour `#FF008000` is carried as computed-style on the rect command |
| 2 | `04_border_widths` | 4 fill ops; each differing-width side is a separate **fill** rect, e.g. `#FFFF0000 at (0,0 112x2)` and `#FF0000FF at (0,52 112x6)` | 2 fill ops; no per-side border ops emitted |
| 3 | `08_text_on_bg` | background fill `#FFFFFF00 at (0,0 200x20)` | `#FFFFFF00 at (0,0 200x18)` — 2 px shorter (line-height leaking from the layout stage into paint) |
| 4 | `10_opacity` | `#80FF0000` — element `opacity:0.5` folded into the paint alpha | `#FFFF0000` — opacity kept as a separate style property, never applied to the recorded colour |
| 5 | `14_outline` | `drawRect style=Stroke #FFFF0000 width=3`, border-box `(-2,-2 106x56)` — outline sits **outside** the border box | no outline op; synthesised from `outline-width` at `(0,0 100x50)`, i.e. the offset is not represented |
| 6 | `15_body_background` | 2 fills — `body`'s `#204060` is **propagated to the viewport canvas** | 3 fills — `#FF204060` painted as an `(0,0 800x50)` body box only; no canvas propagation |
| 7 | `16_inline_text_runs` | text run "mid" x=`49`, "right" x=`79` | x=`45`, x=`75` — 4 px advance-width deficit accumulating per preceding inline run |
| 8 | `18_overflow_clip` | 2 fills — the fully-occluded `#f0f0f0` container fill is dropped | 3 fills — `#FFF0F0F0 at (0,0 100x40)` recorded (Chrome-side occlusion culling, not necessarily a Simple defect) |

The structural headline is finding 1: **Simple's Draw IR has no border, outline
or per-side border-edge command.** Those are style properties on the component
command, and the backend re-derives the primitives at raster time. Chrome
records them as first-class paint ops. That is an architectural divergence at
the paint boundary, not a numeric one, and it is why Simple records 88 ops where
Chrome records 68 while still emitting fewer *primitives*.

Findings 4, 5 and 6 would each need a change under `src/lib/**` (opacity
folding, outline offset geometry, body→canvas background propagation). Per the
current lane constraint those are **reported, not fixed, here**.

## Files

| file | role |
|---|---|
| `chrome_paint_dump.js` | CDP extractor; Skia ops → canonical model |
| `simple_paint_dump.spl` | runs Simple's paint pipeline, emits DrawIR as JSON |
| `paint_diff.js` | lifts both sides, matches ops, writes the report |
| `run_paint_diff.shs` | driver |
| `fixtures/*.html` | 18 paint-focused fixtures (fills, borders, radius, opacity, text runs, clip) |
| `CONTRACT.md` | the stage I/O contract |

Sibling stages: `tools/web_diff` (DOM + cascade), `tools/layout_diff`
(layout + text). Spec:
`test/03_system/browser_engine/chrome_paint_differential_spec.spl`.
