# Gradient Stops Paint Specification

> Tests covering emu_draw_linear_gradient_stops N-stop + angle, emu_draw_radial_gradient_stops N-stop radial.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gradient Stops Paint Specification

## Scenarios

### emu_draw_linear_gradient_stops N-stop + angle

#### paints a 3-stop vertical (180deg) gradient with each row an exact stop

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- paints a 3-stop vertical (180deg) gradient with each row an exact stop
   - Expected: b.init(4, 3) is true
   - Expected: p[0 * 4 + 0] equals `RED`
   - Expected: p[1 * 4 + 0] equals `GREEN`
   - Expected: p[2 * 4 + 0] equals `BLUE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints a 3-stop vertical (180deg) gradient with each row an exact stop")
var b = SoftwareBackend.create()
expect(b.init(4, 3)).to_equal(true)
b.clear(BLACK)
val colors: [u32] = [RED, GREEN, BLUE]
val positions: [i32] = [0, 500, 1000]
emu_draw_linear_gradient_stops(b, 0, 0, 4, 3, colors, positions, 180)
val p = b.read_pixels()
expect(p[0 * 4 + 0]).to_equal(RED)
expect(p[1 * 4 + 0]).to_equal(GREEN)
expect(p[2 * 4 + 0]).to_equal(BLUE)
b.shutdown()
```

</details>

#### paints a 45-degree (non-cardinal) angled gradient with the correct axis

- paints a 45-degree (non-cardinal) angled gradient with the correct axis
   - Expected: b.init(5, 5) is true
   - Expected: p[0 * 5 + 4] equals `WHITE)     # top-right: axis end`
   - Expected: p[4 * 5 + 0] equals `BLACK)      # bottom-left: axis start`
   - Expected: p[0 * 5 + 0] equals `MID_GRAY)   # top-left: perpendicular midpoint`
   - Expected: p[4 * 5 + 4] equals `MID_GRAY)   # bottom-right: perpendicular midpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints a 45-degree (non-cardinal) angled gradient with the correct axis")
# On a square, a 45deg gradient's axis runs from the bottom-left
# corner (position 0) to the top-right corner (position 1000); the
# other two corners (top-left, bottom-right) sit exactly on the
# perpendicular through the center, i.e. at position 500 (mid-gray
# for a black->white gradient) by construction.
var b = SoftwareBackend.create()
expect(b.init(5, 5)).to_equal(true)
b.clear(0xFF123456u32)
val colors: [u32] = [BLACK, WHITE]
val positions: [i32] = [0, 1000]
emu_draw_linear_gradient_stops(b, 0, 0, 5, 5, colors, positions, 45)
val p = b.read_pixels()
expect(p[0 * 5 + 4]).to_equal(WHITE)     # top-right: axis end
expect(p[4 * 5 + 0]).to_equal(BLACK)      # bottom-left: axis start
expect(p[0 * 5 + 0]).to_equal(MID_GRAY)   # top-left: perpendicular midpoint
expect(p[4 * 5 + 4]).to_equal(MID_GRAY)   # bottom-right: perpendicular midpoint
b.shutdown()
```

</details>

#### falls back to a flat fill for a single stop

- falls back to a flat fill for a single stop
   - Expected: b.init(4, 4) is true
   - Expected: p[2 * 4 + 2] equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to a flat fill for a single stop")
var b = SoftwareBackend.create()
expect(b.init(4, 4)).to_equal(true)
b.clear(BLACK)
val colors: [u32] = [RED]
val positions: [i32] = [0]
emu_draw_linear_gradient_stops(b, 0, 0, 4, 4, colors, positions, 90)
val p = b.read_pixels()
expect(p[2 * 4 + 2]).to_equal(RED)
b.shutdown()
```

</details>

### emu_draw_radial_gradient_stops N-stop radial

#### paints center/middle/edge stops at their exact distances

- paints center/middle/edge stops at their exact distances
   - Expected: b.init(24, 24) is true
   - Expected: p[10 * 24 + 10] equals `RED)     # center: distance 0`
   - Expected: p[10 * 24 + 12] equals `GREEN)   # distance 2 == half radius`
   - Expected: p[10 * 24 + 14] equals `BLUE)    # distance 4 == radius (edge`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints center/middle/edge stops at their exact distances")
var b = SoftwareBackend.create()
expect(b.init(24, 24)).to_equal(true)
b.clear(0xFF123456u32)
val colors: [u32] = [RED, GREEN, BLUE]
val positions: [i32] = [0, 500, 1000]
emu_draw_radial_gradient_stops(b, 10, 10, 4, colors, positions)
val p = b.read_pixels()
expect(p[10 * 24 + 10]).to_equal(RED)     # center: distance 0
expect(p[10 * 24 + 12]).to_equal(GREEN)   # distance 2 == half radius
expect(p[10 * 24 + 14]).to_equal(BLUE)    # distance 4 == radius (edge)
b.shutdown()
```

</details>

#### paints a single point for radius <= 0

- paints a single point for radius <= 0
   - Expected: b.init(4, 4) is true
   - Expected: p[2 * 4 + 2] equals `RED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints a single point for radius <= 0")
var b = SoftwareBackend.create()
expect(b.init(4, 4)).to_equal(true)
b.clear(BLACK)
val colors: [u32] = [RED, BLUE]
val positions: [i32] = [0, 1000]
emu_draw_radial_gradient_stops(b, 2, 2, 0, colors, positions)
val p = b.read_pixels()
expect(p[2 * 4 + 2]).to_equal(RED)
b.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering emu_draw_linear_gradient_stops N-stop + angle, emu_draw_radial_gradient_stops N-stop radial.
- emu_draw_linear_gradient_stops N-stop + angle
- emu_draw_radial_gradient_stops N-stop radial

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `75842b6a1f8a19a6ee7f39f099b08bad8db0a017b48eb40d59ddfd767958409b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75842b6a1f8a19a6ee7f39f099b08bad8db0a017b48eb40d59ddfd767958409b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75842b6a1f8a19a6ee7f39f099b08bad8db0a017b48eb40d59ddfd767958409b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints a 3-stop vertical (180deg) gradient with each row an exact stop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints a 45-degree (non-cardinal) angled gradient with the correct axis' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/gradient_stops_paint_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to a flat fill for a single stop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
