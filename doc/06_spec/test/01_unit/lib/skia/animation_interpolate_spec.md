# Skia Animation Interpolate Specification

> Tests for linear interpolation (f64 + color) and cubic-bezier easing curves — mirroring Chromium's gfx::Tween and the CSS cubic-bezier timing function.

<!-- sdn-diagram:id=animation_interpolate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=animation_interpolate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

animation_interpolate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=animation_interpolate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for linear interpolation (f64 + color) and cubic-bezier easing curves —
mirroring Chromium's gfx::Tween and the CSS cubic-bezier timing function.

## Scenarios

### animation_interpolate

#### lerp_f64: t=0 returns a, t=1 returns b, t=0.5 returns average

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val curve = ease_in_cubic()
val y = evaluate_cubic_bezier(curve, 0.5)
expect(y).to_be_less_than(0.5)
expect(y).to_be_greater_than(0.0)
```

</details>

#### evaluate_cubic_bezier: ease_out_cubic at t=0.5 is greater than 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val curve = ease_out_cubic()
val y = evaluate_cubic_bezier(curve, 0.5)
expect(y).to_be_greater_than(0.5)
expect(y).to_be_less_than(1.0)
```

</details>

#### apply_easing: EaseInOut is symmetric around t=0.5 (roughly)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
