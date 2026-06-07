# f32 Precision Tracking Specification

> Regression test for the f32 precision tracking fix that mirrors the W5-I `Value::UInt { value, width }` u32 wrap fix.

<!-- sdn-diagram:id=f32_precision_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=f32_precision_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

f32_precision_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=f32_precision_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# f32 Precision Tracking Specification

Regression test for the f32 precision tracking fix that mirrors the W5-I `Value::UInt { value, width }` u32 wrap fix.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-F32-PRECISION |
| Category | Interpreter |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/f32_precision_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for the f32 precision tracking fix that mirrors the W5-I
`Value::UInt { value, width }` u32 wrap fix.

Before this fix, the Rust seed interpreter held all floats as `Value::Float(f64)`
with no width tag, so `f32`-typed expressions were silently promoted to `f64`.
The classic IEEE 754 distinguishing test
    `0.1f32 + 0.2f32 - 0.3f32`
returned `5.551115123125783e-17` (the f64 error) instead of the correct
single-precision value `0.0f32` (because in f32 the rounding of `0.1 + 0.2`
produces exactly `0.3`, and the difference is zero).

The fix adds `Value::Float32(f32)` and routes f32 literals + arithmetic ops
(Add/Sub/Mul/Div/Mod/Pow/Neg) through native `f32` math via the new
`float_kind()` helper in `interpreter/expr/ops.rs`.

## Scenarios

### f32 precision tracking

#### 0.1f32 + 0.2f32 - 0.3f32 == 0.0 (f32 IEEE 754, not f64 5.55e-17)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: f32 = 0.1f32 + 0.2f32
val r: f32 = a - 0.3f32
# In f32 the rounding cancels exactly: result is +0.0.
# Before the fix, this returned 5.551e-17 (the f64 error).
expect(r == 0.0f32).to_equal(true)
```

</details>

#### f32 mantissa boundary: 16777216f32 + 1f32 == 16777216f32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2^24 = 16777216; f32 mantissa cannot represent 2^24 + 1.
# f64 would give 16777217 — so this is a f32-specific behavior pin.
val r: f32 = 16777216.0f32 + 1.0f32
expect(r == 16777216.0f32).to_equal(true)
```

</details>

#### f32 overflow multiplies to +inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1e30 * 1e30 = 1e60, which overflows f32 max (~3.4e38).
val a: f32 = 1.0e30f32
val r: f32 = a * a
expect(r > 3.4e38f32).to_equal(true)
```

</details>

#### f32 div preserves single-precision rounding

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1.0f32 / 3.0f32 in f32 has only ~7 significant digits, distinct from f64.
val r: f32 = 1.0f32 / 3.0f32
val w: f64 = r.to_f64()
val precise: f64 = 1.0f64 / 3.0f64
expect(w == precise).to_equal(false)
```

</details>

#### f32 -> f64 round-trip stays at f32 precision

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1.0000000001 cannot be represented in f32; rounds to 1.0.
val big: f64 = 1.0000000001f64
val small: f32 = big.to_f32()
val back: f64 = small.to_f64()
expect(back == 1.0f64).to_equal(true)
```

</details>

#### f32 negation preserves f32 type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: f32 = 0.5f32
val r: f32 = -a
expect(r == -0.5f32).to_equal(true)
```

</details>

### f64 arithmetic (no regression)

#### 0.1f64 + 0.2f64 - 0.3f64 == 5.551e-17 (classic f64 error pin)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: f64 = 0.1f64 + 0.2f64
val r: f64 = a - 0.3f64
expect(r > 0.0f64).to_equal(true)
expect(r < 1.0e-15f64).to_equal(true)
```

</details>

#### f64 mantissa: 16777217.0 + 1.0 == 16777218.0 (f64 wider than f32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: f64 = 16777217.0f64 + 1.0f64
expect(r == 16777218.0f64).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
