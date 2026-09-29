# Style → Paint Chunk Specification

> I want to hand the browser a laid-out, styled document and get back the flat rect+colour list the existing rasterizer already knows how to paint — the missing link between `render_lane_pipeline_spec.spl`'s proven layout output and `paint_chunk_rasterizer_spec.spl`'s proven pixel consumer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style → Paint Chunk Specification

I want to hand the browser a laid-out, styled document and get back the flat rect+colour list the existing rasterizer already knows how to paint — the missing link between `render_lane_pipeline_spec.spl`'s proven layout output and `paint_chunk_rasterizer_spec.spl`'s proven pixel consumer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/paint/style_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

I want to hand the browser a laid-out, styled document and get back the flat
rect+colour list the existing rasterizer already knows how to paint — the
missing link between `render_lane_pipeline_spec.spl`'s proven layout output
and `paint_chunk_rasterizer_spec.spl`'s proven pixel consumer.

Up to now `StyledLayout` carried computed rects and resolved styles, but
nothing turned that into `PaintChunkRects` — the array-of-ints shape the
rasterizer walks. These examples build a real HTML+CSS document through the
same pipeline the render-lane spec proves, run it through
`paint_chunks_from_styled_layout`, and assert on the resulting rect and
colour arrays directly.

Deliberately out of scope: pixels. `PaintChunkRects` is inspectable data;
turning it into a framebuffer is a separate, already-proven consumer.

@manual_section Browser Rendering

## Scenarios

### paint_chunks_from_styled_layout

#### emits one opaque rect matching the box's laid-out geometry and colour

- emits one opaque rect matching the box's laid-out geometry and colour
- style a single div red, 100x50, with a 10px margin
- flatten the styled layout into paint rects
- the first div (index 1: body is index 0) sits at its laid-out left/top
   - Expected: rects.rect_x[1] equals `r.0.to_i64()`
   - Expected: rects.rect_y[1] equals `r.1.to_i64()`
   - Expected: "first div laid out" equals `it did not`
- width/height come from CSS, unaffected by margin
   - Expected: rects.rect_w[1] equals `100`
   - Expected: rects.rect_h[1] equals `50`
- colour is packed opaque red, matching the sk_color_argb oracle
   - Expected: rects.colour[1] equals `sk_color_argb(255, 255, 0, 0)`
- body plus both divs each contributed a rect
   - Expected: rects.rect_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits one opaque rect matching the box's laid-out geometry and colour")
step("style a single div red, 100x50, with a 10px margin")
val css = "div { background-color: red; width: 100px; height: 50px; margin: 10px; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("flatten the styled layout into paint rects")
val rects = paint_chunks_from_styled_layout(layout)

step("the first div (index 1: body is index 0) sits at its laid-out left/top")
match layout.rect_for(2):
    Some(r):
        expect(rects.rect_x[1]).to_equal(r.0.to_i64())
        expect(rects.rect_y[1]).to_equal(r.1.to_i64())
    None:
        expect("first div laid out").to_equal("it did not")

step("width/height come from CSS, unaffected by margin")
expect(rects.rect_w[1]).to_equal(100)
expect(rects.rect_h[1]).to_equal(50)

step("colour is packed opaque red, matching the sk_color_argb oracle")
expect(rects.colour[1]).to_equal(sk_color_argb(255, 255, 0, 0))

step("body plus both divs each contributed a rect")
expect(rects.rect_count).to_equal(3)
```

</details>

#### contributes no rect for a display:none element

- contributes no rect for a display:none element
- hide the second div through the stylesheet
- flatten the styled layout into paint rects
- only body and the visible div contributed a rect
   - Expected: rects.rect_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contributes no rect for a display:none element")
step("hide the second div through the stylesheet")
val css = "div { background-color: blue; width: 100px; height: 20px; } .b { display: none; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("flatten the styled layout into paint rects")
val rects = paint_chunks_from_styled_layout(layout)

step("only body and the visible div contributed a rect")
expect(rects.rect_count).to_equal(2)
```

</details>

#### still emits a rect for a box with an unset (transparent) background

- still emits a rect for a box with an unset (transparent) background
- lay out a div with no background-color declared
- flatten the styled layout into paint rects
- no skip-optimization: every box's rect exists, with fully transparent colour
   - Expected: rects.rect_count equals `3`
   - Expected: rects.colour[0] equals `0`
   - Expected: rects.colour[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still emits a rect for a box with an unset (transparent) background")
step("lay out a div with no background-color declared")
val css = "div { width: 40px; height: 20px; }"
val layout = build_styled_layout(_page_tree(), _sheet(css), 800.0, 600.0)

step("flatten the styled layout into paint rects")
val rects = paint_chunks_from_styled_layout(layout)

step("no skip-optimization: every box's rect exists, with fully transparent colour")
expect(rects.rect_count).to_equal(3)
expect(rects.colour[0]).to_equal(0)
expect(rects.colour[1]).to_equal(0)
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
- `REQ-BLINK-STYLE-PAINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a16ea970669f2d605c8294e9432d7282c60e3e10588683b4fc683ab3720e4276`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a16ea970669f2d605c8294e9432d7282c60e3e10588683b4fc683ab3720e4276`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a16ea970669f2d605c8294e9432d7282c60e3e10588683b4fc683ab3720e4276`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/blink/paint/style_paint_spec.spl
mirror: doc/06_spec/unit/lib/blink/paint/style_paint_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/lib/blink/paint/style_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/paint/style_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/paint/style_paint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/paint/style_paint_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/blink/paint/style_paint_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits one opaque rect matching the box's laid-out geometry and colour' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/style_paint_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contributes no rect for a display:none element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/style_paint_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still emits a rect for a box with an unset (transparent) background' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
