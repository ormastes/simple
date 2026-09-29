# Engine2d Baremetal Core Specification

> Tests covering Engine2DBaremetalCore no-op guards, clip that fully excludes the draw, stroked rect (outline only), stroked circle (outline only), gradient_rect single-row fallback, draw_line direction branches, draw_image, draw_codes12_block.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Baremetal Core Specification

## Scenarios

### Engine2DBaremetalCore no-op guards

#### draw_rect_filled with zero width does not touch the buffer

- draw_rect_filled with zero width does not touch the buffer
   - Expected: _px(core, 1, 1) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_rect_filled with zero width does not touch the buffer")
var core = create_buffer_engine_core(6, 6)
core.clear(0xFF000000u32)
core.draw_rect_filled(1, 1, 0, 4, 0xFFFFFFFFu32)
expect(_px(core, 1, 1)).to_equal(0xFF000000u32)
```

</details>

#### draw_rect_filled with negative height does not touch the buffer

- draw_rect_filled with negative height does not touch the buffer
   - Expected: _px(core, 1, 1) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_rect_filled with negative height does not touch the buffer")
var core = create_buffer_engine_core(6, 6)
core.clear(0xFF000000u32)
core.draw_rect_filled(1, 1, 4, -2, 0xFFFFFFFFu32)
expect(_px(core, 1, 1)).to_equal(0xFF000000u32)
```

</details>

#### draw_rect_stroked with zero height is a no-op

- draw_rect_stroked with zero height is a no-op
   - Expected: _px(core, 1, 1) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_rect_stroked with zero height is a no-op")
var core = create_buffer_engine_core(6, 6)
core.clear(0xFF000000u32)
core.draw_rect_stroked(1, 1, 4, 0, 0xFFFFFFFFu32)
expect(_px(core, 1, 1)).to_equal(0xFF000000u32)
```

</details>

#### gradient_rect with zero width is a no-op

- gradient_rect with zero width is a no-op
   - Expected: _px(core, 1, 1) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gradient_rect with zero width is a no-op")
var core = create_buffer_engine_core(6, 6)
core.clear(0xFF000000u32)
core.gradient_rect(1, 1, 0, 4, 0xFFFFFFFFu32, 0xFF000000u32)
expect(_px(core, 1, 1)).to_equal(0xFF000000u32)
```

</details>

### clip that fully excludes the draw

#### a draw entirely outside the clip rect paints nothing

- a draw entirely outside the clip rect paints nothing
   - Expected: _px(core, 5, 5) equals `0xFF000000u32`
   - Expected: _px(core, 6, 6) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a draw entirely outside the clip rect paints nothing")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.set_clip(0, 0, 2, 2)
core.draw_rect_filled(5, 5, 2, 2, 0xFFFFFFFFu32)
core.clear_clip()
expect(_px(core, 5, 5)).to_equal(0xFF000000u32)
expect(_px(core, 6, 6)).to_equal(0xFF000000u32)
```

</details>

### stroked rect (outline only)

#### draw_rect_stroked paints the border but not the interior

- draw_rect_stroked paints the border but not the interior
   - Expected: _px(core, 1, 1) equals `0xFFFF0000u32`
   - Expected: _px(core, 4, 1) equals `0xFFFF0000u32`
   - Expected: _px(core, 1, 4) equals `0xFFFF0000u32`
   - Expected: _px(core, 4, 4) equals `0xFFFF0000u32`
   - Expected: _px(core, 2, 2) equals `0xFF000000u32`
   - Expected: _px(core, 3, 3) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_rect_stroked paints the border but not the interior")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_rect_stroked(1, 1, 4, 4, 0xFFFF0000u32)
# Corners and edge midpoints: painted.
expect(_px(core, 1, 1)).to_equal(0xFFFF0000u32)
expect(_px(core, 4, 1)).to_equal(0xFFFF0000u32)
expect(_px(core, 1, 4)).to_equal(0xFFFF0000u32)
expect(_px(core, 4, 4)).to_equal(0xFFFF0000u32)
# Interior: untouched.
expect(_px(core, 2, 2)).to_equal(0xFF000000u32)
expect(_px(core, 3, 3)).to_equal(0xFF000000u32)
```

</details>

#### draw_rect is an alias for draw_rect_stroked (same outline-only result)

- draw_rect is an alias for draw_rect_stroked (same outline-only result)
   - Expected: _px(core, 1, 1) equals `0xFFFF0000u32`
   - Expected: _px(core, 2, 2) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_rect is an alias for draw_rect_stroked (same outline-only result)")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_rect(1, 1, 4, 4, 0xFFFF0000u32)
expect(_px(core, 1, 1)).to_equal(0xFFFF0000u32)
expect(_px(core, 2, 2)).to_equal(0xFF000000u32)
```

</details>

### stroked circle (outline only)

#### draw_circle_stroked paints the ring but not the center

- draw_circle_stroked paints the ring but not the center
   - Expected: _px(core, 9, 6) equals `0xFF00FF00u32`
   - Expected: _px(core, 3, 6) equals `0xFF00FF00u32`
   - Expected: _px(core, 6, 9) equals `0xFF00FF00u32`
   - Expected: _px(core, 6, 3) equals `0xFF00FF00u32`
   - Expected: _px(core, 6, 6) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_circle_stroked paints the ring but not the center")
var core = create_buffer_engine_core(12, 12)
core.clear(0xFF000000u32)
core.draw_circle_stroked(6, 6, 3, 0xFF00FF00u32)
# Cardinal perimeter points at radius 3.
expect(_px(core, 9, 6)).to_equal(0xFF00FF00u32)
expect(_px(core, 3, 6)).to_equal(0xFF00FF00u32)
expect(_px(core, 6, 9)).to_equal(0xFF00FF00u32)
expect(_px(core, 6, 3)).to_equal(0xFF00FF00u32)
# Center: untouched (unlike draw_circle_filled).
expect(_px(core, 6, 6)).to_equal(0xFF000000u32)
```

</details>

#### draw_circle is an alias for draw_circle_stroked

- draw_circle is an alias for draw_circle_stroked
   - Expected: _px(core, 6, 6) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_circle is an alias for draw_circle_stroked")
var core = create_buffer_engine_core(12, 12)
core.clear(0xFF000000u32)
core.draw_circle(6, 6, 3, 0xFF00FF00u32)
expect(_px(core, 6, 6)).to_equal(0xFF000000u32)
```

</details>

#### draw_circle_filled with r<=0 is a no-op

- draw_circle_filled with r<=0 is a no-op
   - Expected: _px(core, 4, 4) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_circle_filled with r<=0 is a no-op")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_circle_filled(4, 4, 0, 0xFFFFFFFFu32)
expect(_px(core, 4, 4)).to_equal(0xFF000000u32)
```

</details>

### gradient_rect single-row fallback

#### a 1-row gradient paints the top color, not a lerp

- a 1-row gradient paints the top color, not a lerp
   - Expected: _px(core, 0, 0) equals `0xFFAABBCCu32`
   - Expected: _px(core, 3, 0) equals `0xFFAABBCCu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a 1-row gradient paints the top color, not a lerp")
var core = create_buffer_engine_core(4, 4)
core.clear(0xFF000000u32)
core.gradient_rect(0, 0, 4, 1, 0xFFAABBCCu32, 0xFF112233u32)
expect(_px(core, 0, 0)).to_equal(0xFFAABBCCu32)
expect(_px(core, 3, 0)).to_equal(0xFFAABBCCu32)
```

</details>

### draw_line direction branches

#### draws a line going up-left (negative dx and dy)

- draws a line going up-left (negative dx and dy)
   - Expected: _px(core, 5, 5) equals `0xFF00FF00u32`
   - Expected: _px(core, 2, 2) equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draws a line going up-left (negative dx and dy)")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_line(5, 5, 2, 2, 0xFF00FF00u32, 1)
expect(_px(core, 5, 5)).to_equal(0xFF00FF00u32)
expect(_px(core, 2, 2)).to_equal(0xFF00FF00u32)
```

</details>

#### draws a steep line (dy > dx) hitting the y-step branch repeatedly

- draws a steep line (dy > dx) hitting the y-step branch repeatedly
   - Expected: _px(core, 1, 0) equals `0xFF00FF00u32`
   - Expected: _px(core, 2, 6) equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draws a steep line (dy > dx) hitting the y-step branch repeatedly")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_line(1, 0, 2, 6, 0xFF00FF00u32, 1)
expect(_px(core, 1, 0)).to_equal(0xFF00FF00u32)
expect(_px(core, 2, 6)).to_equal(0xFF00FF00u32)
```

</details>

#### thickness<=0 falls back to a 1px line

- thickness<=0 falls back to a 1px line
   - Expected: _px(core, 0, 0) equals `0xFF00FF00u32`
   - Expected: _px(core, 3, 0) equals `0xFF00FF00u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("thickness<=0 falls back to a 1px line")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_line(0, 0, 3, 0, 0xFF00FF00u32, 0)
expect(_px(core, 0, 0)).to_equal(0xFF00FF00u32)
expect(_px(core, 3, 0)).to_equal(0xFF00FF00u32)
```

</details>

### draw_image

#### a solid-color image collapses to one run per row

- a solid-color image collapses to one run per row
   - Expected: _px(core, 1, 1) equals `0xFFFF00FFu32`
   - Expected: _px(core, 2, 1) equals `0xFFFF00FFu32`
   - Expected: _px(core, 1, 2) equals `0xFFFF00FFu32`
   - Expected: _px(core, 2, 2) equals `0xFFFF00FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a solid-color image collapses to one run per row")
var core = create_buffer_engine_core(6, 6)
core.clear(0xFF000000u32)
var pixels: [u32] = [0xFFFF00FFu32; 4]
core.draw_image(1, 1, 2, 2, pixels)
expect(_px(core, 1, 1)).to_equal(0xFFFF00FFu32)
expect(_px(core, 2, 1)).to_equal(0xFFFF00FFu32)
expect(_px(core, 1, 2)).to_equal(0xFFFF00FFu32)
expect(_px(core, 2, 2)).to_equal(0xFFFF00FFu32)
```

</details>

#### a two-color row image paints each color at the right column

- a two-color row image paints each color at the right column
   - Expected: _px(core, 0, 0) equals `0xFFFF0000u32`
   - Expected: _px(core, 1, 0) equals `0xFF0000FFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a two-color row image paints each color at the right column")
var core = create_buffer_engine_core(6, 6)
core.clear(0xFF000000u32)
# 2x1 image: left pixel red, right pixel blue -> two runs of length 1.
var pixels: [u32] = [0xFFFF0000u32, 0xFF0000FFu32]
core.draw_image(0, 0, 2, 1, pixels)
expect(_px(core, 0, 0)).to_equal(0xFFFF0000u32)
expect(_px(core, 1, 0)).to_equal(0xFF0000FFu32)
```

</details>

#### draw_image with zero width is a no-op

- draw_image with zero width is a no-op
   - Expected: _px(core, 0, 0) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_image with zero width is a no-op")
var core = create_buffer_engine_core(4, 4)
core.clear(0xFF000000u32)
var pixels: [u32] = []
core.draw_image(0, 0, 0, 3, pixels)
expect(_px(core, 0, 0)).to_equal(0xFF000000u32)
```

</details>

### draw_codes12_block

#### paints a cell for a non-space code and skips space/zero codes

- paints a cell for a non-space code and skips space/zero codes
   - Expected: _px(core, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _px(core, 5, 7) equals `0xFFFFFFFFu32`
   - Expected: _px(core, 7, 0) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints a cell for a non-space code and skips space/zero codes")
var core = create_buffer_engine_core(40, 10)
core.clear(0xFF000000u32)
# slot 0 = 'A' (65, non-space) painted; slot 1 = 32 (space) skipped;
# slot 2 = 0 skipped; remaining slots space.
core.draw_codes12_block(0, 0, 65, 32, 0, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0xFFFFFFFFu32, 0)
# Default cell (scale<=0): cell_w=6, cell_h=8. Slot 0 spans x in [0,6).
expect(_px(core, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_px(core, 5, 7)).to_equal(0xFFFFFFFFu32)
# Slot 1 (space, skipped): its cell at x in [7,13) stays background.
expect(_px(core, 7, 0)).to_equal(0xFF000000u32)
```

</details>

#### scale>0 changes the cell size to scale*3 by scale*5

- scale>0 changes the cell size to scale*3 by scale*5
   - Expected: _px(core, 0, 0) equals `0xFFFFFFFFu32`
   - Expected: _px(core, 5, 9) equals `0xFFFFFFFFu32`
   - Expected: _px(core, 0, 10) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scale>0 changes the cell size to scale*3 by scale*5")
var core = create_buffer_engine_core(20, 20)
core.clear(0xFF000000u32)
core.draw_codes12_block(0, 0, 65, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 0xFFFFFFFFu32, 2)
# scale=2 -> cell_w=6, cell_h=10. Slot 0 spans x in [0,6), y in [0,10).
expect(_px(core, 0, 0)).to_equal(0xFFFFFFFFu32)
expect(_px(core, 5, 9)).to_equal(0xFFFFFFFFu32)
expect(_px(core, 0, 10)).to_equal(0xFF000000u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2DBaremetalCore no-op guards, clip that fully excludes the draw, stroked rect (outline only), stroked circle (outline only), gradient_rect single-row fallback, draw_line direction branches, draw_image, draw_codes12_block.
- Engine2DBaremetalCore no-op guards
- clip that fully excludes the draw
- stroked rect (outline only)
- stroked circle (outline only)
- gradient_rect single-row fallback
- draw_line direction branches
- draw_image
- draw_codes12_block

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c8a5a4ecd8bbd06faa7e200a33e57f9e8eb8d073799b002a22b8527fd17e48b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8a5a4ecd8bbd06faa7e200a33e57f9e8eb8d073799b002a22b8527fd17e48b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8a5a4ecd8bbd06faa7e200a33e57f9e8eb8d073799b002a22b8527fd17e48b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/engine2d_baremetal_core_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/engine2d_baremetal_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/engine2d_baremetal_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_filled with zero width does not touch the buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_filled with negative height does not touch the buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_baremetal_core_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_stroked with zero height is a no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
