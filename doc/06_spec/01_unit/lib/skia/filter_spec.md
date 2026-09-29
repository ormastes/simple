# Filter Specification

> Tests covering Gaussian kernel, Horizontal blur, Color matrix filter, Drop shadow, Gaussian blur end-to-end.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Filter Specification

## Scenarios

### Gaussian kernel

#### sums to approximately 1.0 for sigma=1.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sums to approximately 1.0 for sigma=1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums to approximately 1.0 for sigma=1.0")
val k = gaussian_kernel(1.0)
val s = _sum_kernel(k)
expect _approx(s, 1.0) to_equal true
```

</details>

#### sums to approximately 1.0 for sigma=2.0

- sums to approximately 1.0 for sigma=2.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums to approximately 1.0 for sigma=2.0")
val k = gaussian_kernel(2.0)
val s = _sum_kernel(k)
expect _approx(s, 1.0) to_equal true
```

</details>

#### returns single element [1.0] for sigma=0.0

- returns single element [1.0] for sigma=0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single element [1.0] for sigma=0.0")
val k = gaussian_kernel(0.0)
expect k.len() to_equal 1
```

</details>

#### kernel is symmetric for sigma=1.5

- kernel is symmetric for sigma=1.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("kernel is symmetric for sigma=1.5")
val k = gaussian_kernel(1.5)
val n = k.len().to_i32()
var ok = true
var i = 0
while i < n / 2:
    val diff = k[i.to_i64()] - k[(n - 1 - i).to_i64()]
    val ad = if diff < 0.0: -diff else: diff
    if ad > 0.000001:
        ok = false
    i = i + 1
expect ok to_equal true
```

</details>

### Horizontal blur

#### spreads color to neighbors from single white pixel

- spreads color to neighbors from single white pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spreads color to neighbors from single white pixel")
val buf = _white_center_5x5()
val blurred = blur_horizontal(buf, 1.0)
val center = blurred.pixels[12]
val neighbor = blurred.pixels[11]
expect center.r < 1.0 to_equal true
expect neighbor.r > 0.0 to_equal true
```

</details>

#### preserves buffer dimensions

- preserves buffer dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves buffer dimensions")
val buf = _white_center_5x5()
val blurred = blur_horizontal(buf, 1.0)
expect blurred.width to_equal 5
expect blurred.height to_equal 5
```

</details>

### Color matrix filter

<details>
<summary>Advanced: identity matrix returns input unchanged</summary>

#### identity matrix returns input unchanged

- identity matrix returns input unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identity matrix returns input unchanged")
val src = SkColor4f(r: 0.4, g: 0.6, b: 0.2, a: 1.0)
val buf = ImageBuffer(width: 1, height: 1, pixels: [src])
val result = apply_color_matrix(buf, _identity_matrix())
expect _approx(result.pixels[0].r, 0.4) to_equal true
expect _approx(result.pixels[0].g, 0.6) to_equal true
expect _approx(result.pixels[0].b, 0.2) to_equal true
expect _approx(result.pixels[0].a, 1.0) to_equal true
```

</details>


</details>

<details>
<summary>Advanced: clamps results to 1.0 when matrix doubles channels</summary>

#### clamps results to 1.0 when matrix doubles channels

- clamps results to 1.0 when matrix doubles channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps results to 1.0 when matrix doubles channels")
val matrix = [2.0, 0.0, 0.0, 0.0, 0.0,
              0.0, 2.0, 0.0, 0.0, 0.0,
              0.0, 0.0, 2.0, 0.0, 0.0,
              0.0, 0.0, 0.0, 2.0, 0.0]
val src = SkColor4f(r: 0.8, g: 0.8, b: 0.8, a: 0.8)
val buf = ImageBuffer(width: 1, height: 1, pixels: [src])
val result = apply_color_matrix(buf, matrix)
expect result.pixels[0].r to_equal 1.0
```

</details>


</details>

<details>
<summary>Advanced: clamps results to 0.0 when matrix negates channels</summary>

#### clamps results to 0.0 when matrix negates channels

- clamps results to 0.0 when matrix negates channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps results to 0.0 when matrix negates channels")
val matrix = [-1.0, 0.0, 0.0, 0.0, 0.0,
               0.0, -1.0, 0.0, 0.0, 0.0,
               0.0, 0.0, -1.0, 0.0, 0.0,
               0.0, 0.0, 0.0, 1.0, 0.0]
val src = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val buf = ImageBuffer(width: 1, height: 1, pixels: [src])
val result = apply_color_matrix(buf, matrix)
expect result.pixels[0].r to_equal 0.0
```

</details>


</details>

### Drop shadow

#### result has same dimensions as source

- result has same dimensions as source


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result has same dimensions as source")
val src = _white_center_5x5()
val shadow_color = SkColor4f(r: 0.0, g: 0.0, b: 0.0, a: 1.0)
val result = drop_shadow(src, 1.0, 1.0, 0.5, 0.5, shadow_color)
expect result.width to_equal 5
expect result.height to_equal 5
```

</details>

#### result pixel count matches source

- result pixel count matches source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result pixel count matches source")
val src = _white_center_5x5()
val shadow_color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val result = drop_shadow(src, 1.0, 1.0, 0.3, 0.3, shadow_color)
expect result.pixels.len() to_equal 25
```

</details>

### Gaussian blur end-to-end

#### two-pass blur spreads energy from single white pixel

- two-pass blur spreads energy from single white pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two-pass blur spreads energy from single white pixel")
val buf = _white_center_5x5()
val result = gaussian_blur(buf, 1.0, 1.0)
val center = result.pixels[12]
val corner = result.pixels[0]
expect center.r < 1.0 to_equal true
expect corner.r > 0.0 to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/filter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Gaussian kernel, Horizontal blur, Color matrix filter, Drop shadow, Gaussian blur end-to-end.
- Gaussian kernel
- Horizontal blur
- Color matrix filter
- Drop shadow
- Gaussian blur end-to-end

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `3bf902fc446b5856fb9b8fb408c37a0f65b1662db18e1cacc23c2072c324dda8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bf902fc446b5856fb9b8fb408c37a0f65b1662db18e1cacc23c2072c324dda8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bf902fc446b5856fb9b8fb408c37a0f65b1662db18e1cacc23c2072c324dda8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/filter_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/filter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/filter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/filter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/filter_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums to approximately 1.0 for sigma=1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/filter_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums to approximately 1.0 for sigma=2.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/filter_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns single element [1.0] for sigma=0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
