# Render Lane: HTML+CSS To Actual Pixels

> `render_lane_pipeline_spec.spl` proves HTML+CSS become correctly-positioned, correctly-coloured layout boxes. `style_paint_spec.spl` proves those boxes flatten into `PaintChunkRects`. Neither goes all the way to a framebuffer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Lane: HTML+CSS To Actual Pixels

`render_lane_pipeline_spec.spl` proves HTML+CSS become correctly-positioned, correctly-coloured layout boxes. `style_paint_spec.spl` proves those boxes flatten into `PaintChunkRects`. Neither goes all the way to a framebuffer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/01_unit/lib/blink/render_lane_pixels_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`render_lane_pipeline_spec.spl` proves HTML+CSS become correctly-positioned,
correctly-coloured layout boxes. `style_paint_spec.spl` proves those boxes
flatten into `PaintChunkRects`. Neither goes all the way to a framebuffer.

These examples run the FULL lane: HTML token stream -> DOM -> CSS tokenize ->
parse -> cascade -> `StyledLayout` -> `paint_chunks_from_styled_layout` ->
`paint_chunk_rasterizer_run` -> real pixels in a `ChunkRasterBuffer`, and
assert on the pixel values themselves, not on intermediate rects.

Scope: background-color + geometry only, matching what the cascade actually
resolves for this lane. No text, no borders, no gradients — those are not
part of `paint_chunks_from_styled_layout`'s output and are out of scope here.

@manual_section Browser Rendering

## Scenarios

### HTML+CSS through to real pixels

#### paints the div's rect red at its laid-out position

- paints the div's rect red at its laid-out position
- run the full lane through to a rasterized buffer
- the div occupies [10,110)x[10,60): its origin, an interior point, and the last in-bounds pixel
   - Expected: buf.get(10, 10) equals `red`
   - Expected: buf.get(60, 35) equals `red`
   - Expected: buf.get(109, 59) equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints the div's rect red at its laid-out position")
step("run the full lane through to a rasterized buffer")
val layout = build_styled_layout(_page_tree(), _sheet(_css()), 200.0, 100.0)
val rects = paint_chunks_from_styled_layout(layout)
val buf = rasterize(rects)

step("the div occupies [10,110)x[10,60): its origin, an interior point, and the last in-bounds pixel")
val red = sk_color_argb(255, 255, 0, 0)
expect(buf.get(10, 10)).to_equal(red)
expect(buf.get(60, 35)).to_equal(red)
expect(buf.get(109, 59)).to_equal(red)
```

</details>

#### paints the body's background blue on pixels the div does not cover

- paints the body's background blue on pixels the div does not cover
- run the full lane through to a rasterized buffer
- a point well outside the div's box is body-blue, not div-red
   - Expected: buf.get(150, 80) equals `blue`
   - Expected: buf.get(199, 99) equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints the body's background blue on pixels the div does not cover")
step("run the full lane through to a rasterized buffer")
val layout = build_styled_layout(_page_tree(), _sheet(_css()), 200.0, 100.0)
val rects = paint_chunks_from_styled_layout(layout)
val buf = rasterize(rects)

step("a point well outside the div's box is body-blue, not div-red")
val blue = sk_color_argb(255, 0, 0, 255)
expect(buf.get(150, 80)).to_equal(blue)
expect(buf.get(199, 99)).to_equal(blue)
```

</details>

#### the boundary just outside the div's right/bottom edge is blue, not red

- the boundary just outside the div's right/bottom edge is blue, not red
- run the full lane through to a rasterized buffer
- row/column just outside the div's [10,110)x[10,60) box is body-blue
   - Expected: buf.get(9, 30) equals `blue`
   - Expected: buf.get(30, 9) equals `blue`
   - Expected: buf.get(110, 30) equals `blue`
   - Expected: buf.get(60, 60) equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the boundary just outside the div's right/bottom edge is blue, not red")
step("run the full lane through to a rasterized buffer")
val layout = build_styled_layout(_page_tree(), _sheet(_css()), 200.0, 100.0)
val rects = paint_chunks_from_styled_layout(layout)
val buf = rasterize(rects)

step("row/column just outside the div's [10,110)x[10,60) box is body-blue")
val blue = sk_color_argb(255, 0, 0, 255)
expect(buf.get(9, 30)).to_equal(blue)
expect(buf.get(30, 9)).to_equal(blue)
expect(buf.get(110, 30)).to_equal(blue)
expect(buf.get(60, 60)).to_equal(blue)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-RENDER-LANE-PIXELS-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cf86e6ba691181d5d9896076c42068b0cf4938acc895b2c15187d49520c73c88`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf86e6ba691181d5d9896076c42068b0cf4938acc895b2c15187d49520c73c88`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf86e6ba691181d5d9896076c42068b0cf4938acc895b2c15187d49520c73c88`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/blink/render_lane_pixels_spec.spl
mirror: doc/06_spec/01_unit/lib/blink/render_lane_pixels_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/blink/render_lane_pixels_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/blink/render_lane_pixels_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/blink/render_lane_pixels_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/blink/render_lane_pixels_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints the div's rect red at its laid-out position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/render_lane_pixels_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints the body's background blue on pixels the div does not cover' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/blink/render_lane_pixels_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the boundary just outside the div's right/bottom edge is blue, not red' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
