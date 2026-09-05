# Text Glyph Paint Specification

> `paint_chunks_from_styled_layout` paints one flat background rect per box and nothing else — text nodes contribute no glyph pixels at all. That was blink's exit-criterion-2 blocker: `browser_render_lane_spec.spl` had an example proving a `<p>Hello</p>` page painted zero non-white pixels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Glyph Paint Specification

`paint_chunks_from_styled_layout` paints one flat background rect per box and nothing else — text nodes contribute no glyph pixels at all. That was blink's exit-criterion-2 blocker: `browser_render_lane_spec.spl` had an example proving a `<p>Hello</p>` page painted zero non-white pixels.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/paint/text_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`paint_chunks_from_styled_layout` paints one flat background rect per box and
nothing else — text nodes contribute no glyph pixels at all. That was blink's
exit-criterion-2 blocker: `browser_render_lane_spec.spl` had an example
proving a `<p>Hello</p>` page painted zero non-white pixels.

`blink.paint.text_paint` closes it with a real, if low-fidelity, glyph
rasterizer: the shared 8x16 VGA bitmap font
(`common.ui.glyph_bitmap_8x16`, the same font SimpleOS's framebuffer driver
and host WM chrome text already use), one opaque 1x1 rect per "on" bit,
painted through `blink_render_html_to_pixel_array` end to end.

These examples render real pixels and assert directly on the buffer — not on
`PaintChunkRects` counts — so a regression that reaches all the way to the
adapter's return value is caught, matching the sabotage-resistant style of
`browser_render_lane_spec.spl`.

@manual_section Browser Rendering

## Scenarios

### blink paints real glyph pixels for text nodes

#### paints zero non-white pixels for a page with no text content at all

- paints zero non-white pixels for a page with no text content at all
- render a page whose only content is an empty, unstyled body
- the whole 40 x 20 = 800 pixel buffer is untouched white page
   - Expected: pixels.len() equals `VIEW_PIXELS`
   - Expected: _count(pixels, WHITE) equals `VIEW_PIXELS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints zero non-white pixels for a page with no text content at all")
step("render a page whose only content is an empty, unstyled body")
val pixels = blink_render_html_to_pixel_array(_page(""), VIEW_W, VIEW_H)

step("the whole 40 x 20 = 800 pixel buffer is untouched white page")
expect(pixels.len()).to_equal(VIEW_PIXELS)
expect(_count(pixels, WHITE)).to_equal(VIEW_PIXELS)
```

</details>

#### paints a real, non-uniform glyph pattern for a single letter — sabotage oracle

- paints a real, non-uniform glyph pattern for a single letter — sabotage oracle
- render a page whose only content is the single letter H
- more than one pixel differs from the white background
   - Expected: painted > 10 is true
   - Expected: painted < 128 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints a real, non-uniform glyph pattern for a single letter — sabotage oracle")
step("render a page whose only content is the single letter H")
val pixels = blink_render_html_to_pixel_array(_page("<p>H</p>"), VIEW_W, VIEW_H)

step("more than one pixel differs from the white background")
# A no-op / silently-skipped glyph paint step would leave EVERY pixel
# white (as the empty-body example above proves is the actual
# baseline). The 8x16 'H' bitmap
# (0xC6,0xC6,0xC6,0xC6,0xC6,0xFE,0xC6,0xC6,0xC6,0xC6,...) sets a
# specific, uneven set of bits — not a solid block — so a fill-the-
# whole-cell-black shortcut would ALSO fail this: it would paint 128
# pixels (8x16), while the real 'H' glyph sets far fewer bits than
# that per row. This is the sabotage-resistant assertion: it fails
# both on "nothing painted" and on "something painted but not really
# glyph-shaped".
val painted = _non_white_count(pixels)
expect(painted > 10).to_equal(true)
expect(painted < 128).to_equal(true)
```

</details>

#### paints strictly more non-white pixels for a longer text run

- paints strictly more non-white pixels for a longer text run
- render one page with a single character and one with a whole word
- two glyphs paint strictly more coverage than one — proves per-character work, not a fixed stamp
   - Expected: _non_white_count(one_word) > _non_white_count(one_char) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints strictly more non-white pixels for a longer text run")
step("render one page with a single character and one with a whole word")
val one_char = blink_render_html_to_pixel_array(_page("<p>H</p>"), VIEW_W, VIEW_H)
val one_word = blink_render_html_to_pixel_array(_page("<p>Hi</p>"), VIEW_W, VIEW_H)

step("two glyphs paint strictly more coverage than one — proves per-character work, not a fixed stamp")
expect(_non_white_count(one_word) > _non_white_count(one_char)).to_equal(true)
```

</details>

#### paints glyphs in the element's resolved text color, not an arbitrary fixed color

- paints glyphs in the element's resolved text color, not an arbitrary fixed color
- render the same letter styled red and styled blue
- the red render has red pixels the blue render does not, and vice versa
   - Expected: _count(red_pixels, red_argb) > 0 is true
   - Expected: _count(blue_pixels, blue_argb) > 0 is true
   - Expected: _count(red_pixels, blue_argb) equals `0`
   - Expected: _count(blue_pixels, red_argb) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints glyphs in the element's resolved text color, not an arbitrary fixed color")
step("render the same letter styled red and styled blue")
val red_page = "<html><body><style>body { background-color: white; width: 40px; height: 20px; }" +
    "p { color: red; }</style><p>H</p></body></html>"
val blue_page = "<html><body><style>body { background-color: white; width: 40px; height: 20px; }" +
    "p { color: blue; }</style><p>H</p></body></html>"
val red_pixels = blink_render_html_to_pixel_array(red_page, VIEW_W, VIEW_H)
val blue_pixels = blink_render_html_to_pixel_array(blue_page, VIEW_W, VIEW_H)

step("the red render has red pixels the blue render does not, and vice versa")
val red_argb: u32 = 4294901760u32   # opaque red
val blue_argb: u32 = 4278190335u32  # opaque blue
expect(_count(red_pixels, red_argb) > 0).to_equal(true)
expect(_count(blue_pixels, blue_argb) > 0).to_equal(true)
expect(_count(red_pixels, blue_argb)).to_equal(0)
expect(_count(blue_pixels, red_argb)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-TEXT-PAINT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `713e472ca69ab954cd12121e2dd24e994bdd3cd4fbc153a79f642ea60ec2d641`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `713e472ca69ab954cd12121e2dd24e994bdd3cd4fbc153a79f642ea60ec2d641`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `713e472ca69ab954cd12121e2dd24e994bdd3cd4fbc153a79f642ea60ec2d641`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/blink/paint/text_paint_spec.spl
mirror: doc/06_spec/unit/lib/blink/paint/text_paint_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/lib/blink/paint/text_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/paint/text_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/paint/text_paint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/paint/text_paint_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/blink/paint/text_paint_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints zero non-white pixels for a page with no text content at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/text_paint_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints a real, non-uniform glyph pattern for a single letter — sabotage oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/paint/text_paint_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints strictly more non-white pixels for a longer text run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
