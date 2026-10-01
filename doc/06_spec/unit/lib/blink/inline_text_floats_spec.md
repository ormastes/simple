# Blink Inline Text: Line Boxes Shortened by Floats

> Until now blink wrapped a text run to one rectangular width and knew nothing

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink Inline Text: Line Boxes Shortened by Floats

Until now blink wrapped a text run to one rectangular width and knew nothing

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink / Layout |
| Status | Implemented |
| Plan | doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7) |
| Source | `test/unit/lib/blink/inline_text_floats_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Until now blink wrapped a text run to one rectangular width and knew nothing
about floats, so a paragraph set beside a floated image was drawn straight
THROUGH it. `block_flow.spl` recorded this as the most user-visible gap it had.
`layout_inline_text_around` closes it: each line box asks the float area what
width is available at its own y and is laid out at that width, from that x.

The audience is anyone changing `blink/layout/inline_text.spl`. Line-box
geometry is what a reader actually sees, so every case below asserts concrete
pixel coordinates and explains the arithmetic behind each one.

## Scope and Preconditions

Every case sets 16px monospace text with no extra letter or word spacing. Under
`common/layout/text_metrics.spl` that resolves to a glyph scale of `16 / 8 = 2`,
and therefore:

| Metric | Value | Where it comes from |
|--------|-------|---------------------|
| Cell advance | 10px | `5 * scale` = `5 * 2` |
| Space advance | 5px | `advance / 2` = `10 / 2` |
| Line height | 18px | `9 * scale` = `9 * 2` |

So a four-letter word costs 40px, a space costs 5px, and each line box is 18px
tall. Every expected number below is built from those three.

Runs are made of four-letter words (`aaaa bbbb cccc ...`) precisely so the
arithmetic stays legible: the width of a run of *n* such words is
`n * 40 + (n - 1) * 5`.

## Primary Workflow

Build a `FloatArea`, add the float margin rects, then call
`layout_inline_text_around(run, font, area, start_y, container_left,
container_right)`. Read `lines` for the per-line rects, `bottom_px` for where to
carry on stacking, and `widest_px` for the intrinsic width.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Per-line band | Each line is measured over `[y, y + 18)`, not at a single scanline |
| Shortened AND shifted | A left float moves the line's left edge right and takes width off it |
| Closed band | A line with zero available width is not emitted; the cursor drops 18px |
| Truncating cast | The f64 band becomes an i64 wrap limit by truncation, which can only narrow |

## Compatibility and Limitations

Still monospace-only, no bidi, no shaping. `block_flow.spl` does not yet call
this: `BlockFlowBox` carries no text, so the caller owning the run passes the
box's float area in. Floats still do not escape their parent, so the area a
line consults is its own box's.

## Scenarios

### a run set beside a left float two lines tall

#### narrows and indents the lines it overlaps and restores full width below it

- narrows and indents the lines it overlaps and restores full width below it
- Put a 60x36 left float at the top-left of a 200-wide container
- Lay out ten four-letter words from y = 0 across that container
- Three line boxes come out
- The first line starts past the float and is shortened by it
- The second line is still inside the float's band, so it matches
- The third line clears the float and gets the whole container
- The block reports where the next box may start, and its widest line


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrows and indents the lines it overlaps and restores full width below it")
step("Put a 60x36 left float at the top-left of a 200-wide container")
# 36px is exactly two 18px line boxes, so the float covers lines 1 and 2
# and stops precisely where line 3 begins.
val area = float_area_new()
area.add(float_rect(0.0, 0.0, 60.0, 36.0, FloatSide.Left))

step("Lay out ten four-letter words from y = 0 across that container")
val run = "aaaa bbbb cccc dddd eeee ffff gggg hhhh iiii jjjj"
val block = layout_inline_text_around(run, font16(), area, 0.0, 0.0, 200.0)

step("Three line boxes come out")
# Lines 1 and 2 get 140px each and fit three words; the remaining four
# words fit on the full-width third line.
assert_eq(block.lines.len(), 3)

step("The first line starts past the float and is shortened by it")
# The float's right edge is 60, so the line starts at 60 and the band
# left is 200 - 60 = 140.
val l0 = block.lines[0]
assert_true(approx_eq(l0.left_px, 60.0))
assert_true(approx_eq(l0.top_px, 0.0))
assert_true(approx_eq(l0.width_px, 140.0))
assert_true(approx_eq(l0.height_px, 18.0))
# Three words cost 3*40 + 2*5 = 130, which fits in 140; a fourth would
# need 130 + 5 + 40 = 175 and does not.
assert_eq(l0.content, "aaaa bbbb cccc")

step("The second line is still inside the float's band, so it matches")
# Its band is [18, 36), which still overlaps the float ending at 36.
val l1 = block.lines[1]
assert_true(approx_eq(l1.left_px, 60.0))
assert_true(approx_eq(l1.top_px, 18.0))
assert_true(approx_eq(l1.width_px, 140.0))
assert_eq(l1.content, "dddd eeee ffff")

step("The third line clears the float and gets the whole container")
# Its band is [36, 54). The float's bottom is exactly 36 and the overlap
# test is half-open, so the float no longer excludes anything here:
# left goes back to 0 and the width back to the full 200.
val l2 = block.lines[2]
assert_true(approx_eq(l2.left_px, 0.0))
assert_true(approx_eq(l2.top_px, 36.0))
assert_true(approx_eq(l2.width_px, 200.0))
# Four words cost 4*40 + 3*5 = 175, which fits in 200.
assert_eq(l2.content, "gggg hhhh iiii jjjj")

step("The block reports where the next box may start, and its widest line")
# Three 18px lines from y = 0 end at 54. The widest line is the last, at
# 175px of actual ink.
assert_true(approx_eq(block.bottom_px, 54.0))
assert_true(approx_eq(block.widest_px, 175.0))
```

</details>

### a run set beside a right float one line tall

#### keeps the line at the container's left edge but shortens it

- keeps the line at the container's left edge but shortens it
- Put a 60-wide right float across the first line only
- Lay out six four-letter words from y = 0 across a 200-wide container
- The first line stays at x = 0 but is only 140 wide
- The second line is below the float and gets the full 200


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the line at the container's left edge but shortens it")
step("Put a 60-wide right float across the first line only")
# Its margin box is x 140..200, y 0..18 — exactly one line box tall.
val area = float_area_new()
area.add(float_rect(140.0, 0.0, 200.0, 18.0, FloatSide.Right))

step("Lay out six four-letter words from y = 0 across a 200-wide container")
val run = "aaaa bbbb cccc dddd eeee ffff"
val block = layout_inline_text_around(run, font16(), area, 0.0, 0.0, 200.0)

step("The first line stays at x = 0 but is only 140 wide")
# A right float pulls the RIGHT edge in from 200 to 140; the left edge
# is untouched, so the line starts at 0 with a band of 140 - 0 = 140.
val l0 = block.lines[0]
assert_true(approx_eq(l0.left_px, 0.0))
assert_true(approx_eq(l0.width_px, 140.0))
# Three words = 130 fit; four = 175 do not.
assert_eq(l0.content, "aaaa bbbb cccc")

step("The second line is below the float and gets the full 200")
val l1 = block.lines[1]
assert_true(approx_eq(l1.left_px, 0.0))
assert_true(approx_eq(l1.top_px, 18.0))
assert_true(approx_eq(l1.width_px, 200.0))
assert_eq(l1.content, "dddd eeee ffff")
```

</details>

### a run whose first line is completely blocked by floats

#### emits no line there and resumes below the floats instead of overlapping them

- emits no line there and resumes below the floats instead of overlapping them
- Close the whole first line with a left float and a right float that meet
- Lay out three four-letter words from y = 0
- Exactly one line comes out, and it is at y = 18, not y = 0
- The block therefore ends at 36, one line box below where it started


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits no line there and resumes below the floats instead of overlapping them")
step("Close the whole first line with a left float and a right float that meet")
# Left float occupies 0..100 and the right float 100..200, both y 0..18,
# so the available width over [0, 18) is 100 - 100 = 0.
val area = float_area_new()
area.add(float_rect(0.0, 0.0, 100.0, 18.0, FloatSide.Left))
area.add(float_rect(100.0, 0.0, 200.0, 18.0, FloatSide.Right))

step("Lay out three four-letter words from y = 0")
val run = "aaaa bbbb cccc"
val block = layout_inline_text_around(run, font16(), area, 0.0, 0.0, 200.0)

step("Exactly one line comes out, and it is at y = 18, not y = 0")
# Nothing can be set in a zero-width band, so the cursor drops one line
# height rather than emitting text on top of the floats.
assert_eq(block.lines.len(), 1)
val l0 = block.lines[0]
assert_true(approx_eq(l0.top_px, 18.0))
assert_true(approx_eq(l0.left_px, 0.0))
assert_true(approx_eq(l0.width_px, 200.0))
assert_eq(l0.content, "aaaa bbbb cccc")

step("The block therefore ends at 36, one line box below where it started")
assert_true(approx_eq(block.bottom_px, 36.0))
```

</details>

### a run laid out with an empty float area

#### produces the same lines as the plain rectangular wrapper

- produces the same lines as the plain rectangular wrapper
- Wrap six words to 140px with no floats, both ways
- Both agree on the line count and on every line's text
- Every line spans the whole container, since nothing excludes it
- The two lines stack 18px apart and the block ends at 36


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces the same lines as the plain rectangular wrapper")
step("Wrap six words to 140px with no floats, both ways")
val run = "aaaa bbbb cccc dddd eeee ffff"
val area = float_area_new()
val around = layout_inline_text_around(run, font16(), area, 0.0, 0.0, 140.0)
val plain = layout_inline_text(run, 140, font16())

step("Both agree on the line count and on every line's text")
assert_eq(around.lines.len(), plain.lines.len())
assert_eq(around.lines[0].content, plain.lines[0])
assert_eq(around.lines[1].content, plain.lines[1])

step("Every line spans the whole container, since nothing excludes it")
assert_true(approx_eq(around.lines[0].left_px, 0.0))
assert_true(approx_eq(around.lines[0].width_px, 140.0))
assert_true(approx_eq(around.lines[1].left_px, 0.0))

step("The two lines stack 18px apart and the block ends at 36")
assert_true(approx_eq(around.lines[0].top_px, 0.0))
assert_true(approx_eq(around.lines[1].top_px, 18.0))
assert_true(approx_eq(around.bottom_px, 36.0))
```

</details>

### an empty run

#### still occupies exactly one line box so the paragraph keeps its height

- still occupies exactly one line box so the paragraph keeps its height
- Lay out the empty string in an empty 200-wide container from y = 0
- One empty line box comes out, 18px tall and full width
- It has no ink, so the intrinsic width is zero and the block ends at 18


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still occupies exactly one line box so the paragraph keeps its height")
step("Lay out the empty string in an empty 200-wide container from y = 0")
val area = float_area_new()
val block = layout_inline_text_around("", font16(), area, 0.0, 0.0, 200.0)

step("One empty line box comes out, 18px tall and full width")
assert_eq(block.lines.len(), 1)
assert_eq(block.lines[0].content, "")
assert_true(approx_eq(block.lines[0].height_px, 18.0))
assert_true(approx_eq(block.lines[0].width_px, 200.0))

step("It has no ink, so the intrinsic width is zero and the block ends at 18")
assert_true(approx_eq(block.widest_px, 0.0))
assert_true(approx_eq(block.bottom_px, 18.0))
```

</details>

### a left float that begins below the first line

#### leaves the first line full width and shortens only the lines it crosses

- leaves the first line full width and shortens only the lines it crosses
- Put a 60-wide left float from y = 18 to y = 36
- Lay out eight four-letter words from y = 0 across 200px
- The first line is untouched: full width, four words
- The second line is indented and shortened by the float


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the first line full width and shortens only the lines it crosses")
step("Put a 60-wide left float from y = 18 to y = 36")
# Range queries are the point here: a float that starts one line down
# must not affect the line above it, and must fully affect the one it
# covers.
val area = float_area_new()
area.add(float_rect(0.0, 18.0, 60.0, 36.0, FloatSide.Left))

step("Lay out eight four-letter words from y = 0 across 200px")
val run = "aaaa bbbb cccc dddd eeee ffff gggg hhhh"
val block = layout_inline_text_around(run, font16(), area, 0.0, 0.0, 200.0)

step("The first line is untouched: full width, four words")
# Band [0, 18) does not reach the float's top at 18, so the width is the
# full 200 and four words (175px) fit.
val l0 = block.lines[0]
assert_true(approx_eq(l0.left_px, 0.0))
assert_true(approx_eq(l0.width_px, 200.0))
assert_eq(l0.content, "aaaa bbbb cccc dddd")

step("The second line is indented and shortened by the float")
val l1 = block.lines[1]
assert_true(approx_eq(l1.top_px, 18.0))
assert_true(approx_eq(l1.left_px, 60.0))
assert_true(approx_eq(l1.width_px, 140.0))
assert_eq(l1.content, "eeee ffff gggg")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BLINK-LAYOUT-LINEBOX-FLOATS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89fd29182456b541dd787f48e5fc0a3f79301b45cb10139d8d2c7d2f73d1d45a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89fd29182456b541dd787f48e5fc0a3f79301b45cb10139d8d2c7d2f73d1d45a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89fd29182456b541dd787f48e5fc0a3f79301b45cb10139d8d2c7d2f73d1d45a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/blink/inline_text_floats_spec.spl
mirror: doc/06_spec/unit/lib/blink/inline_text_floats_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/unit/lib/blink/inline_text_floats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/inline_text_floats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/inline_text_floats_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/blink/inline_text_floats_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'narrows and indents the lines it overlaps and restores full width below it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/inline_text_floats_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the line at the container's left edge but shortens it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/inline_text_floats_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits no line there and resumes below the floats instead of overlapping them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
