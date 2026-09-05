# Blend Specification

> Tests covering Porter-Duff: blend_clear, Porter-Duff: blend_src, Porter-Duff: blend_dst, Porter-Duff: blend_src_over, Porter-Duff: blend_plus, Porter-Duff: blend_modulate, Porter-Duff: blend_screen, Compose dispatcher.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blend Specification

## Scenarios

### Porter-Duff: blend_clear

#### returns all-zero regardless of inputs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns all-zero regardless of inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all-zero regardless of inputs")
val r = blend_clear(_white(), _red())
expect r.r to_equal 0.0
expect r.g to_equal 0.0
expect r.b to_equal 0.0
expect r.a to_equal 0.0
```

</details>

### Porter-Duff: blend_src

#### returns src unchanged, ignores dst

- returns src unchanged, ignores dst


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns src unchanged, ignores dst")
val r = blend_src(_red(), _white())
expect r.r to_equal 1.0
expect r.g to_equal 0.0
expect r.b to_equal 0.0
expect r.a to_equal 1.0
```

</details>

### Porter-Duff: blend_dst

#### returns dst unchanged, ignores src

- returns dst unchanged, ignores src


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns dst unchanged, ignores src")
val r = blend_dst(_red(), _white())
expect r.r to_equal 1.0
expect r.g to_equal 1.0
expect r.b to_equal 1.0
expect r.a to_equal 1.0
```

</details>

### Porter-Duff: blend_src_over

#### with fully opaque src returns src

- with fully opaque src returns src


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with fully opaque src returns src")
val r = blend_src_over(_red(), _white())
expect r.r to_equal 1.0
expect r.g to_equal 0.0
expect r.b to_equal 0.0
expect r.a to_equal 1.0
```

</details>

#### with fully transparent src returns dst

- with fully transparent src returns dst


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with fully transparent src returns dst")
val transparent = SkColor4f(r: 0.5, g: 0.3, b: 0.1, a: 0.0)
val dst = _red()
val r = blend_src_over(transparent, dst)
expect _approx(r.r, 1.0) to_equal true
expect _approx(r.g, 0.0) to_equal true
expect _approx(r.a, 1.0) to_equal true
```

</details>

#### with half-alpha blends proportionally

- with half-alpha blends proportionally


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with half-alpha blends proportionally")
val src = SkColor4f(r: 0.0, g: 0.0, b: 1.0, a: 0.5)
val dst = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val r = blend_src_over(src, dst)
expect _approx(r.b, 0.5) to_equal true
expect _approx(r.r, 0.5) to_equal true
```

</details>

### Porter-Duff: blend_plus

#### caps summed channels at 1.0

- caps summed channels at 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caps summed channels at 1.0")
val r = blend_plus(_white(), _white())
expect r.r to_equal 1.0
expect r.a to_equal 1.0
```

</details>

#### adds channels below 1.0

- adds channels below 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds channels below 1.0")
val a = SkColor4f(r: 0.3, g: 0.3, b: 0.3, a: 0.3)
val b = SkColor4f(r: 0.4, g: 0.4, b: 0.4, a: 0.4)
val r = blend_plus(a, b)
expect _approx(r.r, 0.7) to_equal true
```

</details>

### Porter-Duff: blend_modulate

#### multiplies channels per-component

- multiplies channels per-component


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiplies channels per-component")
val a = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val b = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val r = blend_modulate(a, b)
expect _approx(r.r, 0.25) to_equal true
```

</details>

### Porter-Duff: blend_screen

#### with black src returns dst

- with black src returns dst


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with black src returns dst")
val r = blend_screen(_black(), _red())
expect _approx(r.r, 1.0) to_equal true
```

</details>

#### screen formula: s + d - s*d

- screen formula: s + d - s*d


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("screen formula: s + d - s*d")
val a = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val b = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val r = blend_screen(a, b)
# 0.5 + 0.5 - 0.25 = 0.75
expect _approx(r.r, 0.75) to_equal true
```

</details>

### Compose dispatcher

#### SrcOver routes correctly

- SrcOver routes correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SrcOver routes correctly")
val r = compose(_red(), _white(), SkBlendMode.SrcOver)
expect r.r to_equal 1.0
expect r.g to_equal 0.0
```

</details>

#### Clear routes to all-zero

- Clear routes to all-zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Clear routes to all-zero")
val r = compose(_white(), _white(), SkBlendMode.Clear)
expect r.r to_equal 0.0
expect r.a to_equal 0.0
```

</details>

#### Multiply routes to multiply mode

- Multiply routes to multiply mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Multiply routes to multiply mode")
val a = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val b = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val direct = blend_multiply(a, b)
val via_compose = compose(a, b, SkBlendMode.Multiply)
expect _approx(direct.r, via_compose.r) to_equal true
```

</details>

#### Screen routes to screen mode

- Screen routes to screen mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Screen routes to screen mode")
val r = compose(_black(), _red(), SkBlendMode.Screen)
expect _approx(r.r, 1.0) to_equal true
```

</details>

#### Src routes to src

- Src routes to src


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Src routes to src")
val r = compose(_red(), _white(), SkBlendMode.Src)
expect r.r to_equal 1.0
expect r.g to_equal 0.0
```

</details>

#### Dst routes to dst

- Dst routes to dst


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Dst routes to dst")
val r = compose(_red(), _white(), SkBlendMode.Dst)
expect r.g to_equal 1.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/blend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Porter-Duff: blend_clear, Porter-Duff: blend_src, Porter-Duff: blend_dst, Porter-Duff: blend_src_over, Porter-Duff: blend_plus, Porter-Duff: blend_modulate, Porter-Duff: blend_screen, Compose dispatcher.
- Porter-Duff: blend_clear
- Porter-Duff: blend_src
- Porter-Duff: blend_dst
- Porter-Duff: blend_src_over
- Porter-Duff: blend_plus
- Porter-Duff: blend_modulate
- Porter-Duff: blend_screen
- Compose dispatcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `eb6592ae693065bf6d9ff45e2666950fcf5f8ef27a5526f798b476a04bd66e79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb6592ae693065bf6d9ff45e2666950fcf5f8ef27a5526f798b476a04bd66e79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb6592ae693065bf6d9ff45e2666950fcf5f8ef27a5526f798b476a04bd66e79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/blend_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/blend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/blend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/blend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/blend_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns all-zero regardless of inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/blend_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns src unchanged, ignores dst' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/blend_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns dst unchanged, ignores src' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
