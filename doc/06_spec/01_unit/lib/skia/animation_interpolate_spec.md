# Skia Animation Interpolate Specification

> Tests for linear interpolation (f64 + color) and cubic-bezier easing curves — mirroring Chromium's gfx::Tween and the CSS cubic-bezier timing function.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Animation Interpolate Specification

Tests for linear interpolation (f64 + color) and cubic-bezier easing curves — mirroring Chromium's gfx::Tween and the CSS cubic-bezier timing function.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-ANI-001 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/animation_interpolate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for linear interpolation (f64 + color) and cubic-bezier easing curves —
mirroring Chromium's gfx::Tween and the CSS cubic-bezier timing function.

## Scenarios

### animation_interpolate

#### lerp_f64: t=0 returns a, t=1 returns b, t=0.5 returns average

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lerp_f64: t=0 returns a, t=1 returns b, t=0.5 returns average
   - Expected: zero_ok is true
   - Expected: one_ok is true
   - Expected: half_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lerp_f64: t=0 returns a, t=1 returns b, t=0.5 returns average")
val a = 10.0
val b = 30.0
val at_zero = lerp_f64(a, b, 0.0)
val at_one = lerp_f64(a, b, 1.0)
val at_half = lerp_f64(a, b, 0.5)
val zero_ok = math_abs(at_zero - 10.0) < 1e-9
val one_ok = math_abs(at_one - 30.0) < 1e-9
val half_ok = math_abs(at_half - 20.0) < 1e-9
expect(zero_ok).to_equal(true)
expect(one_ok).to_equal(true)
expect(half_ok).to_equal(true)
```

</details>

#### lerp_color: component-wise lerp preserves alpha when both inputs have same alpha

- lerp_color: component-wise lerp preserves alpha when both inputs have same alpha
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true
   - Expected: a_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lerp_color: component-wise lerp preserves alpha when both inputs have same alpha")
val c1 = sk_color4f(0.0, 0.0, 0.0, 0.5)
val c2 = sk_color4f(1.0, 1.0, 1.0, 0.5)
val mid = lerp_color(c1, c2, 0.5)
val r_ok = math_abs(mid.r - 0.5) < 1e-9
val g_ok = math_abs(mid.g - 0.5) < 1e-9
val b_ok = math_abs(mid.b - 0.5) < 1e-9
val a_ok = math_abs(mid.a - 0.5) < 1e-9
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

#### evaluate_cubic_bezier: linear curve (0,0,1,1) produces y=x

- evaluate_cubic_bezier: linear curve (0,0,1,1) produces y=x
   - Expected: ok0 is true
   - Expected: ok1 is true
   - Expected: ok2 is true
   - Expected: ok3 is true
   - Expected: ok4 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluate_cubic_bezier: linear curve (0,0,1,1) produces y=x")
val linear = ease_linear()
val y_at_0 = evaluate_cubic_bezier(linear, 0.0)
val y_at_quarter = evaluate_cubic_bezier(linear, 0.25)
val y_at_half = evaluate_cubic_bezier(linear, 0.5)
val y_at_three_quarter = evaluate_cubic_bezier(linear, 0.75)
val y_at_1 = evaluate_cubic_bezier(linear, 1.0)
val ok0 = math_abs(y_at_0 - 0.0) < 1e-6
val ok1 = math_abs(y_at_quarter - 0.25) < 1e-6
val ok2 = math_abs(y_at_half - 0.5) < 1e-6
val ok3 = math_abs(y_at_three_quarter - 0.75) < 1e-6
val ok4 = math_abs(y_at_1 - 1.0) < 1e-6
expect(ok0).to_equal(true)
expect(ok1).to_equal(true)
expect(ok2).to_equal(true)
expect(ok3).to_equal(true)
expect(ok4).to_equal(true)
```

</details>

#### evaluate_cubic_bezier: ease_in_cubic at t=0.5 is less than 0.5

- evaluate_cubic_bezier: ease_in_cubic at t=0.5 is less than 0.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluate_cubic_bezier: ease_in_cubic at t=0.5 is less than 0.5")
val curve = ease_in_cubic()
val y = evaluate_cubic_bezier(curve, 0.5)
expect(y).to_be_less_than(0.5)
expect(y).to_be_greater_than(0.0)
```

</details>

#### evaluate_cubic_bezier: ease_out_cubic at t=0.5 is greater than 0.5

- evaluate_cubic_bezier: ease_out_cubic at t=0.5 is greater than 0.5


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluate_cubic_bezier: ease_out_cubic at t=0.5 is greater than 0.5")
val curve = ease_out_cubic()
val y = evaluate_cubic_bezier(curve, 0.5)
expect(y).to_be_greater_than(0.5)
expect(y).to_be_less_than(1.0)
```

</details>

#### apply_easing: EaseInOut is symmetric around t=0.5 (roughly)

- apply_easing: EaseInOut is symmetric around t=0.5 (roughly)
   - Expected: symmetric is true
   - Expected: mid_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_easing: EaseInOut is symmetric around t=0.5 (roughly)")
val custom = ease_linear()
val y_low = apply_easing(EasingKind.EaseInOut, 0.25, custom)
val y_high = apply_easing(EasingKind.EaseInOut, 0.75, custom)
# Symmetry: f(0.25) + f(0.75) should be approximately 1.0.
val sum = y_low + y_high
val symmetric = math_abs(sum - 1.0) < 0.05
expect(symmetric).to_equal(true)
val y_mid = apply_easing(EasingKind.EaseInOut, 0.5, custom)
val mid_ok = math_abs(y_mid - 0.5) < 1e-6
expect(mid_ok).to_equal(true)
```

</details>

#### apply_easing: Linear returns t unchanged for any t in [0,1]

- apply_easing: Linear returns t unchanged for any t in [0,1]
   - Expected: ok0 is true
   - Expected: ok1 is true
   - Expected: ok2 is true
   - Expected: ok3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("apply_easing: Linear returns t unchanged for any t in [0,1]")
val custom = ease_linear()
val y0 = apply_easing(EasingKind.Linear, 0.0, custom)
val y1 = apply_easing(EasingKind.Linear, 0.33, custom)
val y2 = apply_easing(EasingKind.Linear, 0.66, custom)
val y3 = apply_easing(EasingKind.Linear, 1.0, custom)
val ok0 = math_abs(y0 - 0.0) < 1e-12
val ok1 = math_abs(y1 - 0.33) < 1e-12
val ok2 = math_abs(y2 - 0.66) < 1e-12
val ok3 = math_abs(y3 - 1.0) < 1e-12
expect(ok0).to_equal(true)
expect(ok1).to_equal(true)
expect(ok2).to_equal(true)
expect(ok3).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `102f5cadec7d89f7fbd12baeb33aa22c2bdb723212b9ca32aa22d996d2d63aea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `102f5cadec7d89f7fbd12baeb33aa22c2bdb723212b9ca32aa22d996d2d63aea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `102f5cadec7d89f7fbd12baeb33aa22c2bdb723212b9ca32aa22d996d2d63aea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/animation_interpolate_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/animation_interpolate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/animation_interpolate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/animation_interpolate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/animation_interpolate_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lerp_f64: t=0 returns a, t=1 returns b, t=0.5 returns average' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/animation_interpolate_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lerp_color: component-wise lerp preserves alpha when both inputs have same alpha' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/animation_interpolate_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluate_cubic_bezier: linear curve (0,0,1,1) produces y=x' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
