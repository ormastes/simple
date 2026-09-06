# Engine2d Baremetal Core Parity Specification

> Tests covering Engine2DBaremetalCore buffer-mode raster parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Baremetal Core Parity Specification

## Scenarios

### Engine2DBaremetalCore buffer-mode raster parity

#### opaque fill and clear

#### clear paints every pixel

- clear paints every pixel
   - Expected: _px(core, 0, 0) equals `0xFF010203u32`
   - Expected: _px(core, 7, 7) equals `0xFF010203u32`
   - Expected: _px(core, 4, 3) equals `0xFF010203u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear paints every pixel")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF010203u32)
expect(_px(core, 0, 0)).to_equal(0xFF010203u32)
expect(_px(core, 7, 7)).to_equal(0xFF010203u32)
expect(_px(core, 4, 3)).to_equal(0xFF010203u32)
```

</details>

#### opaque draw_rect_filled fills only the rect

- opaque draw_rect_filled fills only the rect
   - Expected: _px(core, 2, 2) equals `0xFFFF0000u32`
   - Expected: _px(core, 4, 4) equals `0xFFFF0000u32`
   - Expected: _px(core, 1, 1) equals `0xFF000000u32`
   - Expected: _px(core, 5, 5) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opaque draw_rect_filled fills only the rect")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_rect_filled(2, 2, 3, 3, 0xFFFF0000u32)
expect(_px(core, 2, 2)).to_equal(0xFFFF0000u32)
expect(_px(core, 4, 4)).to_equal(0xFFFF0000u32)
expect(_px(core, 1, 1)).to_equal(0xFF000000u32)
expect(_px(core, 5, 5)).to_equal(0xFF000000u32)
```

</details>

#### alpha blending (src-over)

#### 50% white over black yields mid-gray, matching host blend()

- 50% white over black yields mid-gray, matching host blend()
   - Expected: _px(core, 3, 3) equals `0xFF808080u32`
   - Expected: _px(core, 2, 2) equals `0xFF808080u32`
   - Expected: _px(core, 0, 0) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("50% white over black yields mid-gray, matching host blend()")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
# sa=128, out = (255*128 + 0*127)/255 = 128 per channel; out_a = 255.
core.draw_rect_filled(2, 2, 3, 3, 0x80FFFFFFu32)
expect(_px(core, 3, 3)).to_equal(0xFF808080u32)
expect(_px(core, 2, 2)).to_equal(0xFF808080u32)
expect(_px(core, 0, 0)).to_equal(0xFF000000u32)
```

</details>

#### clip rectangle

#### confines all draws to the clip rect

- confines all draws to the clip rect
   - Expected: _px(core, 1, 1) equals `0xFF112233u32`
   - Expected: _px(core, 2, 2) equals `0xFF112233u32`
   - Expected: _px(core, 3, 3) equals `0xFF000000u32`
   - Expected: _px(core, 5, 5) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("confines all draws to the clip rect")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.set_clip(0, 0, 3, 3)
core.draw_rect_filled(0, 0, 8, 8, 0xFF112233u32)
core.clear_clip()
expect(_px(core, 1, 1)).to_equal(0xFF112233u32)
expect(_px(core, 2, 2)).to_equal(0xFF112233u32)
expect(_px(core, 3, 3)).to_equal(0xFF000000u32)
expect(_px(core, 5, 5)).to_equal(0xFF000000u32)
```

</details>

#### 2-color vertical gradient

#### lerps top to bottom matching emu row math

- lerps top to bottom matching emu row math
   - Expected: _px(core, 0, 0) equals `0xFF000000u32`
   - Expected: _px(core, 0, 1) equals `0xFF555555u32`
   - Expected: _px(core, 0, 2) equals `0xFFAAAAAAu32`
   - Expected: _px(core, 1, 3) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lerps top to bottom matching emu row math")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
# h=4, denom=3: rows -> 0, 85, 170, 255 gray.
core.gradient_rect(0, 0, 2, 4, 0xFF000000u32, 0xFFFFFFFFu32)
expect(_px(core, 0, 0)).to_equal(0xFF000000u32)
expect(_px(core, 0, 1)).to_equal(0xFF555555u32)
expect(_px(core, 0, 2)).to_equal(0xFFAAAAAAu32)
expect(_px(core, 1, 3)).to_equal(0xFFFFFFFFu32)
```

</details>

#### line and filled circle

#### horizontal line paints its span only

- horizontal line paints its span only
   - Expected: _px(core, 0, 0) equals `0xFF00FF00u32`
   - Expected: _px(core, 3, 0) equals `0xFF00FF00u32`
   - Expected: _px(core, 4, 0) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("horizontal line paints its span only")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_line(0, 0, 3, 0, 0xFF00FF00u32, 1)
expect(_px(core, 0, 0)).to_equal(0xFF00FF00u32)
expect(_px(core, 3, 0)).to_equal(0xFF00FF00u32)
expect(_px(core, 4, 0)).to_equal(0xFF000000u32)
```

</details>

#### filled circle fills its disk

- filled circle fills its disk
   - Expected: _px(core, 4, 4) equals `0xFF0000FFu32`
   - Expected: _px(core, 2, 4) equals `0xFF0000FFu32`
   - Expected: _px(core, 6, 4) equals `0xFF0000FFu32`
   - Expected: _px(core, 4, 2) equals `0xFF0000FFu32`
   - Expected: _px(core, 4, 6) equals `0xFF0000FFu32`
   - Expected: _px(core, 0, 0) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filled circle fills its disk")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF000000u32)
core.draw_circle_filled(4, 4, 2, 0xFF0000FFu32)
expect(_px(core, 4, 4)).to_equal(0xFF0000FFu32)
expect(_px(core, 2, 4)).to_equal(0xFF0000FFu32)
expect(_px(core, 6, 4)).to_equal(0xFF0000FFu32)
expect(_px(core, 4, 2)).to_equal(0xFF0000FFu32)
expect(_px(core, 4, 6)).to_equal(0xFF0000FFu32)
expect(_px(core, 0, 0)).to_equal(0xFF000000u32)
```

</details>

#### bitmap text is coverage-only

#### paints glyph pixels without clobbering the background

- paints glyph pixels without clobbering the background


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints glyph pixels without clobbering the background")
var core = create_buffer_engine_core(8, 8)
core.clear(0xFF303030u32)
core.draw_text(0, 0, "I", 0xFFFFFFFFu32)
var fg = 0
var bg = 0
var gy = 0
while gy < 7:
    var gx = 0
    while gx < 5:
        val p = _px(core, gx, gy)
        if p == 0xFFFFFFFFu32:
            fg = fg + 1
        if p == 0xFF303030u32:
            bg = bg + 1
        gx = gx + 1
    gy = gy + 1
# At least one lit glyph pixel and at least one preserved background
# pixel inside the glyph box proves a real glyph, not a solid block.
assert_true(fg > 0)
assert_true(bg > 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2DBaremetalCore buffer-mode raster parity.
- Engine2DBaremetalCore buffer-mode raster parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `9aad4e8a23d22d3547ba7eeabf97005544f8167fbef056b86a8c2674724ba4ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9aad4e8a23d22d3547ba7eeabf97005544f8167fbef056b86a8c2674724ba4ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9aad4e8a23d22d3547ba7eeabf97005544f8167fbef056b86a8c2674724ba4ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear paints every pixel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opaque draw_rect_filled fills only the rect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_baremetal_core_parity_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '50% white over black yields mid-gray, matching host blend()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
