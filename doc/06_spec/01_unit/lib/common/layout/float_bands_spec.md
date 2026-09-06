# CSS Float Exclusion Bands and `clear`

> A floated box is taken out of normal flow and pushed to one side of its

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Float Exclusion Bands and `clear`

A floated box is taken out of normal flow and pushed to one side of its

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / Layout |
| Status | Implemented |
| Plan | doc/03_plan/ui/rendering/blink_wiring_plan.md (blocker 7) |
| Source | `test/01_unit/lib/common/layout/float_bands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

A floated box is taken out of normal flow and pushed to one side of its
container; the boxes and lines beside it must then avoid it, and a box with
`clear` must drop below it entirely. This module owns that geometry — where a
new float lands, how wide the space beside the existing floats is at a given
height, and how far down `clear` pushes a box.

The audience is a block-layout driver: `blink/layout/block_flow.spl` today.

## Scope and Preconditions

Pure rectangle arithmetic in `f64` CSS pixels, relative to one containing
block. No DOM, no style record. The caller hands in each float's MARGIN box
(margins already folded in) and asks questions about the space that is left.

Every query is over a vertical RANGE `[y, y + height)`, not a single scanline.
The live lane samples one y, which misses a float that starts just below a tall
block's top edge but overlaps most of it.

## Primary Workflow

Create a `FloatArea`, then for each float call `place_and_add` to find and
record its position; for each in-flow box call `left_edge_at` /
`available_width_at` to see what space remains, and `clearance_for` to honour
`clear`. `lowest_bottom` is what a container's auto height must grow to.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Band | The horizontal space left between the floats over a vertical range |
| Placement search | A float goes as high as possible; if it does not fit it drops to the next float's bottom and retries |
| Clearance | The y a `clear`ing box must start at — never above where it already was |

## Compatibility and Limitations

Floats do not escape the area they are placed in — this module has no notion of
an outer formatting context. No `shape-outside`, no writing-mode-relative
sides, no float shrink-to-fit. A float too wide for any band is placed at the
container edge and allowed to overflow (CSS 2.1 §9.5.1 rule 3).

## Scenarios

### FloatArea with no floats

#### reports the full container width as available

- reports the full container width as available
- Create an empty float area
   - Expected: area.count() equals `0`
- Ask what is available across a 300px-wide container
   - Expected: area.available_width_at(0.0, 20.0, 0.0, 300.0) equals `300.0`
   - Expected: area.left_edge_at(0.0, 20.0, 0.0) equals `0.0`
   - Expected: area.right_edge_at(0.0, 20.0, 300.0) equals `300.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the full container width as available")
step("Create an empty float area")
val area = float_area_new()
assert_true(area.is_empty())
expect(area.count()).to_equal(0)
step("Ask what is available across a 300px-wide container")
# Nothing is excluded, so the band is the container itself: 300 - 0.
expect(area.available_width_at(0.0, 20.0, 0.0, 300.0)).to_equal(300.0)
expect(area.left_edge_at(0.0, 20.0, 0.0)).to_equal(0.0)
expect(area.right_edge_at(0.0, 20.0, 300.0)).to_equal(300.0)
```

</details>

#### reports a zero lowest float bottom

- reports a zero lowest float bottom
- Ask an empty area for its lowest float bottom
   - Expected: area.lowest_bottom() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a zero lowest float bottom")
step("Ask an empty area for its lowest float bottom")
# A container with no floats owes no extra height.
val area = float_area_new()
expect(area.lowest_bottom()).to_equal(0.0)
```

</details>

#### leaves a clearing box exactly where it was

- leaves a clearing box exactly where it was
- Ask for clear: both at y = 40
   - Expected: area.clearance_for(ClearKind.ClearBoth, 40.0) equals `40.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves a clearing box exactly where it was")
step("Ask for clear: both at y = 40")
# `clear` never moves a box UP, and with no floats there is nothing to
# clear, so 40 stays 40.
val area = float_area_new()
expect(area.clearance_for(ClearKind.ClearBoth, 40.0)).to_equal(40.0)
```

</details>

### placing a single float

#### puts a left float flush against the container's left edge at the top

- puts a left float flush against the container's left edge at the top
- Place a 100x50 left float starting at y = 0 in a 0..300 container
   - Expected: f.left equals `0.0`
   - Expected: f.top equals `0.0`
   - Expected: f.right equals `100.0`
   - Expected: f.bottom equals `50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("puts a left float flush against the container's left edge at the top")
step("Place a 100x50 left float starting at y = 0 in a 0..300 container")
val area = float_area_new()
val f = area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
# Nothing is in the way, so it goes as high (y = 0) and as far left
# (x = 0) as it can: left 0, right 0 + 100, bottom 0 + 50.
expect(f.left).to_equal(0.0)
expect(f.top).to_equal(0.0)
expect(f.right).to_equal(100.0)
expect(f.bottom).to_equal(50.0)
```

</details>

#### puts a right float flush against the container's right edge

- puts a right float flush against the container's right edge
- Place a 100x50 right float in the same container
   - Expected: f.right equals `300.0`
   - Expected: f.left equals `200.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("puts a right float flush against the container's right edge")
step("Place a 100x50 right float in the same container")
val area = float_area_new()
val f = area.place_and_add(100.0, 50.0, FloatSide.Right, 0.0, 0.0, 300.0)
# As far RIGHT as it can: its right edge is the container's 300 and its
# left edge is therefore 300 - 100 = 200.
expect(f.right).to_equal(300.0)
expect(f.left).to_equal(200.0)
```

</details>

#### narrows the band beside it but not below it

- narrows the band beside it but not below it
- Place a 100x50 left float, then probe two heights
- Probe a 10px-tall band at y = 0, alongside the float
   - Expected: area.available_width_at(0.0, 10.0, 0.0, 300.0) equals `200.0`
   - Expected: area.left_edge_at(0.0, 10.0, 0.0) equals `100.0`
- Probe a 10px-tall band at y = 60, below the float's bottom of 50
   - Expected: area.available_width_at(60.0, 10.0, 0.0, 300.0) equals `300.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("narrows the band beside it but not below it")
step("Place a 100x50 left float, then probe two heights")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
step("Probe a 10px-tall band at y = 0, alongside the float")
# The float occupies 0..100, so only 100..300 is left: 200px.
expect(area.available_width_at(0.0, 10.0, 0.0, 300.0)).to_equal(200.0)
expect(area.left_edge_at(0.0, 10.0, 0.0)).to_equal(100.0)
step("Probe a 10px-tall band at y = 60, below the float's bottom of 50")
# Past the float entirely, so the full 300 is back.
expect(area.available_width_at(60.0, 10.0, 0.0, 300.0)).to_equal(300.0)
```

</details>

#### narrows a tall box that only partly overlaps the float

- narrows a tall box that only partly overlaps the float
- Place a 100x50 left float, then probe a band from y = 40 to y = 90
   - Expected: area.available_width_at(40.0, 50.0, 0.0, 300.0) equals `200.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("narrows a tall box that only partly overlaps the float")
step("Place a 100x50 left float, then probe a band from y = 40 to y = 90")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
# The band starts at 40, inside the float, and runs to 90, past it. It
# OVERLAPS, so the float still excludes it: 200px, not 300. A
# single-scanline query at the band's midpoint (y = 65) would answer
# 300 and place the box under the float — the exact defect the range
# query exists to avoid.
expect(area.available_width_at(40.0, 50.0, 0.0, 300.0)).to_equal(200.0)
```

</details>

### stacking floats on the same side

#### places a second left float beside the first when it fits

- places a second left float beside the first when it fits
- Place a 100x50 left float, then an 80x30 left float
   - Expected: f2.top equals `0.0`
   - Expected: f2.left equals `100.0`
   - Expected: f2.right equals `180.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("places a second left float beside the first when it fits")
step("Place a 100x50 left float, then an 80x30 left float")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
val f2 = area.place_and_add(80.0, 30.0, FloatSide.Left, 0.0, 0.0, 300.0)
# 200px of band is left at y = 0 and the float needs 80, so it fits
# beside the first one: left edge at the first float's right edge, 100.
expect(f2.top).to_equal(0.0)
expect(f2.left).to_equal(100.0)
expect(f2.right).to_equal(180.0)
```

</details>

#### drops a second float below the first when it does not fit

- drops a second float below the first when it does not fit
- Place a 100x50 left float, then a 250x20 left float
   - Expected: f2.top equals `50.0`
   - Expected: f2.left equals `0.0`
   - Expected: f2.bottom equals `70.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops a second float below the first when it does not fit")
step("Place a 100x50 left float, then a 250x20 left float")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
val f2 = area.place_and_add(250.0, 20.0, FloatSide.Left, 0.0, 0.0, 300.0)
# Only 200px is free at y = 0 and the float wants 250, so the search
# drops to the next band boundary — the first float's bottom, y = 50 —
# where the whole 300 is free, and places it flush left there.
expect(f2.top).to_equal(50.0)
expect(f2.left).to_equal(0.0)
expect(f2.bottom).to_equal(70.0)
```

</details>

#### a left and a right float share the same line when they fit

- a left and a right float share the same line when they fit
- Place a 100-wide left float and a 100-wide right float, both 50 tall
   - Expected: l.top equals `0.0`
   - Expected: r.top equals `0.0`
   - Expected: area.available_width_at(0.0, 10.0, 0.0, 300.0) equals `100.0`
   - Expected: area.left_edge_at(0.0, 10.0, 0.0) equals `100.0`
   - Expected: area.right_edge_at(0.0, 10.0, 300.0) equals `200.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a left and a right float share the same line when they fit")
step("Place a 100-wide left float and a 100-wide right float, both 50 tall")
val area = float_area_new()
val l = area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
val r = area.place_and_add(100.0, 50.0, FloatSide.Right, 0.0, 0.0, 300.0)
# 100 + 100 = 200 <= 300, so both sit at y = 0 and 100px is left
# between them.
expect(l.top).to_equal(0.0)
expect(r.top).to_equal(0.0)
expect(area.available_width_at(0.0, 10.0, 0.0, 300.0)).to_equal(100.0)
expect(area.left_edge_at(0.0, 10.0, 0.0)).to_equal(100.0)
expect(area.right_edge_at(0.0, 10.0, 300.0)).to_equal(200.0)
```

</details>

#### never places a float above the y it was asked to start at

- never places a float above the y it was asked to start at
- Place a float with start_y = 80 in an empty container
   - Expected: f.top equals `80.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never places a float above the y it was asked to start at")
step("Place a float with start_y = 80 in an empty container")
val area = float_area_new()
val f = area.place_and_add(50.0, 20.0, FloatSide.Left, 80.0, 0.0, 300.0)
# "As high as possible" is bounded below by the current flow position:
# a float may not float back up past content already laid out.
expect(f.top).to_equal(80.0)
```

</details>

#### overflows rather than shrinking a float wider than the container

- overflows rather than shrinking a float wider than the container
- Place a 400-wide left float in a 300-wide container
   - Expected: f.left equals `0.0`
   - Expected: f.right equals `400.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overflows rather than shrinking a float wider than the container")
step("Place a 400-wide left float in a 300-wide container")
val area = float_area_new()
val f = area.place_and_add(400.0, 20.0, FloatSide.Left, 0.0, 0.0, 300.0)
# CSS 2.1 §9.5.1 rule 3: it is placed at the container edge and allowed
# to stick out. It keeps its declared 400 width — this module never
# shrinks a float to fit.
expect(f.left).to_equal(0.0)
expect(f.right).to_equal(400.0)
```

</details>

### clearance_for

#### clear: left drops past left floats only

- clear: left drops past left floats only
- Place a left float 0..50 and a right float 0..90, then clear left from 0
   - Expected: area.clearance_for(ClearKind.ClearLeft, 0.0) equals `50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clear: left drops past left floats only")
step("Place a left float 0..50 and a right float 0..90, then clear left from 0")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
area.place_and_add(100.0, 90.0, FloatSide.Right, 0.0, 0.0, 300.0)
# Only the LEFT float matters, and its bottom is 50.
expect(area.clearance_for(ClearKind.ClearLeft, 0.0)).to_equal(50.0)
```

</details>

#### clear: right drops past right floats only

- clear: right drops past right floats only
- Same two floats, clear right from 0
   - Expected: area.clearance_for(ClearKind.ClearRight, 0.0) equals `90.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clear: right drops past right floats only")
step("Same two floats, clear right from 0")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
area.place_and_add(100.0, 90.0, FloatSide.Right, 0.0, 0.0, 300.0)
# The right float's bottom is 90.
expect(area.clearance_for(ClearKind.ClearRight, 0.0)).to_equal(90.0)
```

</details>

#### clear: both drops past the lowest float on either side

- clear: both drops past the lowest float on either side
- Same two floats, clear both from 0
   - Expected: area.clearance_for(ClearKind.ClearBoth, 0.0) equals `90.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clear: both drops past the lowest float on either side")
step("Same two floats, clear both from 0")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
area.place_and_add(100.0, 90.0, FloatSide.Right, 0.0, 0.0, 300.0)
# max(50, 90) = 90.
expect(area.clearance_for(ClearKind.ClearBoth, 0.0)).to_equal(90.0)
```

</details>

#### clear: none leaves the box where it was

- clear: none leaves the box where it was
- Ask for no clearance at y = 20 with a float below it
   - Expected: area.clearance_for(ClearKind.NoClear, 20.0) equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clear: none leaves the box where it was")
step("Ask for no clearance at y = 20 with a float below it")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
expect(area.clearance_for(ClearKind.NoClear, 20.0)).to_equal(20.0)
```

</details>

#### never moves a box up to reach a float it is already past

- never moves a box up to reach a float it is already past
- Clear both from y = 200 with floats ending at 90
   - Expected: area.clearance_for(ClearKind.ClearBoth, 200.0) equals `200.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never moves a box up to reach a float it is already past")
step("Clear both from y = 200 with floats ending at 90")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
area.place_and_add(100.0, 90.0, FloatSide.Right, 0.0, 0.0, 300.0)
# Clearance is max(current y, float bottom) = max(200, 90) = 200.
expect(area.clearance_for(ClearKind.ClearBoth, 200.0)).to_equal(200.0)
```

</details>

### lowest_bottom

#### reports the deepest float on either side

- reports the deepest float on either side
- Place floats ending at 50 and 90
   - Expected: area.lowest_bottom() equals `90.0`
   - Expected: area.lowest_bottom_on(FloatSide.Left) equals `50.0`
   - Expected: area.lowest_bottom_on(FloatSide.Right) equals `90.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the deepest float on either side")
step("Place floats ending at 50 and 90")
val area = float_area_new()
area.place_and_add(100.0, 50.0, FloatSide.Left, 0.0, 0.0, 300.0)
area.place_and_add(100.0, 90.0, FloatSide.Right, 0.0, 0.0, 300.0)
# This is what a container's auto height must reach to contain its own
# floats (CSS 2.1 §10.6.7).
expect(area.lowest_bottom()).to_equal(90.0)
expect(area.lowest_bottom_on(FloatSide.Left)).to_equal(50.0)
expect(area.lowest_bottom_on(FloatSide.Right)).to_equal(90.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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
- `REQ-BLINK-LAYOUT-FLOATS-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36f92e24dca6c35823f41e0e2c3f2618787fb5b837023e981e48adc297766936`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36f92e24dca6c35823f41e0e2c3f2618787fb5b837023e981e48adc297766936`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36f92e24dca6c35823f41e0e2c3f2618787fb5b837023e981e48adc297766936`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/layout/float_bands_spec.spl
mirror: doc/06_spec/01_unit/lib/common/layout/float_bands_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/layout/float_bands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/layout/float_bands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/layout/float_bands_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 38 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/layout/float_bands_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/layout/float_bands_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the full container width as available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/layout/float_bands_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a zero lowest float bottom' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/layout/float_bands_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves a clearing box exactly where it was' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
