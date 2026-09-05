# Shaders Specification

> Tests covering interpolate_stops: midpoint, interpolate_stops: first stop, tile_coord: Repeat, tile_coord: Clamp, tile_coord: Mirror, eval_linear_gradient: start point, eval_linear_gradient: end point, eval_radial_gradient: center, sample_image_nearest: empty pixels, apply_blend: SrcOver with opaque src, apply_blend: Clear.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shaders Specification

## Scenarios

### interpolate_stops: midpoint

#### t=0.5 with two stops returns midpoint color

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- t=0.5 with two stops returns midpoint color


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t=0.5 with two stops returns midpoint color")
val colors = [_red_packed(), _blue_packed()]
val positions = [0.0, 1.0]
val result = interpolate_stops(colors, positions, 0.5)
expect _approx(result.r, 0.5) to_equal true
expect _approx(result.b, 0.5) to_equal true
expect _approx(result.g, 0.0) to_equal true
```

</details>

### interpolate_stops: first stop

#### t=0 returns first stop color

- t=0 returns first stop color


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t=0 returns first stop color")
val colors = [_red_packed(), _blue_packed()]
val positions = [0.0, 1.0]
val result = interpolate_stops(colors, positions, 0.0)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
```

</details>

### tile_coord: Repeat

#### t=1.5 with Repeat returns 0.5

- t=1.5 with Repeat returns 0.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t=1.5 with Repeat returns 0.5")
val result = tile_coord(1.5, SkTileMode.Repeat)
expect _approx(result, 0.5) to_equal true
```

</details>

### tile_coord: Clamp

#### t=1.5 with Clamp returns 1.0

- t=1.5 with Clamp returns 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t=1.5 with Clamp returns 1.0")
val result = tile_coord(1.5, SkTileMode.Clamp)
expect _approx(result, 1.0) to_equal true
```

</details>

### tile_coord: Mirror

#### t=-0.3 with Mirror maps to 0.3

- t=-0.3 with Mirror maps to 0.3


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t=-0.3 with Mirror maps to 0.3")
val result = tile_coord(-0.3, SkTileMode.Mirror)
# tri-wave: -0.3 is in the range [-1,0]; mirror maps to 0.3
val ok = _approx(result, 0.3) or _approx(result, 0.7)
expect ok to_equal true
```

</details>

### eval_linear_gradient: start point

#### at start point returns first stop color

- at start point returns first stop color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("at start point returns first stop color")
val shader = _make_two_stop_shader()
val result = eval_linear_gradient(shader, 0.0, 0.0)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
```

</details>

### eval_linear_gradient: end point

#### at end point returns last stop color

- at end point returns last stop color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("at end point returns last stop color")
val shader = _make_two_stop_shader()
val result = eval_linear_gradient(shader, 100.0, 0.0)
expect _approx(result.r, 0.0) to_equal true
expect _approx(result.b, 1.0) to_equal true
```

</details>

### eval_radial_gradient: center

#### at center returns first stop color

- at center returns first stop color


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("at center returns first stop color")
val shader = _make_radial_shader()
val result = eval_radial_gradient(shader, 50.0, 50.0)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
```

</details>

### sample_image_nearest: empty pixels

#### returns transparent black when pixel list is empty

- returns transparent black when pixel list is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns transparent black when pixel list is empty")
val image = _empty_image()
val result = sample_image_nearest(image, 1.0, 1.0)
expect _approx(result.r, 0.0) to_equal true
expect _approx(result.g, 0.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
expect _approx(result.a, 0.0) to_equal true
```

</details>

### apply_blend: SrcOver with opaque src

#### opaque red over anything returns red

- opaque red over anything returns red


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opaque red over anything returns red")
val src = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val dst = SkColor4f(r: 0.0, g: 1.0, b: 0.0, a: 1.0)
val result = apply_blend(src, dst, SkBlendMode.SrcOver)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.g, 0.0) to_equal true
expect _approx(result.a, 1.0) to_equal true
```

</details>

### apply_blend: Clear

#### Clear returns all-zero

- Clear returns all-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Clear returns all-zero")
val src = SkColor4f(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val dst = SkColor4f(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val result = apply_blend(src, dst, SkBlendMode.Clear)
expect _approx(result.r, 0.0) to_equal true
expect _approx(result.g, 0.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
expect _approx(result.a, 0.0) to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/shaders_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpolate_stops: midpoint, interpolate_stops: first stop, tile_coord: Repeat, tile_coord: Clamp, tile_coord: Mirror, eval_linear_gradient: start point, eval_linear_gradient: end point, eval_radial_gradient: center, sample_image_nearest: empty pixels, apply_blend: SrcOver with opaque src, apply_blend: Clear.
- interpolate_stops: midpoint
- interpolate_stops: first stop
- tile_coord: Repeat
- tile_coord: Clamp
- tile_coord: Mirror
- eval_linear_gradient: start point
- eval_linear_gradient: end point
- eval_radial_gradient: center
- sample_image_nearest: empty pixels
- apply_blend: SrcOver with opaque src
- apply_blend: Clear

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `2a8e0351aeeb41bfd2c6d257cdb575bae559c2dca9b047ce8e48eb8a47e0da8f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a8e0351aeeb41bfd2c6d257cdb575bae559c2dca9b047ce8e48eb8a47e0da8f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a8e0351aeeb41bfd2c6d257cdb575bae559c2dca9b047ce8e48eb8a47e0da8f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/shaders_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/shaders_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/shaders_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/shaders_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/shaders_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 't=0.5 with two stops returns midpoint color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/shaders_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 't=0 returns first stop color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/shaders_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 't=1.5 with Repeat returns 0.5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
