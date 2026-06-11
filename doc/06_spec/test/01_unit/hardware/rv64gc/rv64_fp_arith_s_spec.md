# RV64 Single-Precision FP Arithmetic Tests

> Unit tests for single-precision FP: fadd.s, fsub.s, fmul.s, fdiv.s, fsqrt.s.

<!-- sdn-diagram:id=rv64_fp_arith_s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_arith_s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_arith_s_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_arith_s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Arithmetic Tests

Unit tests for single-precision FP: fadd.s, fsub.s, fmul.s, fdiv.s, fsqrt.s.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-ARITH-S-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_arith_s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for single-precision FP: fadd.s, fsub.s, fmul.s, fdiv.s, fsqrt.s.

## Scenarios

### FADD.S

#### 1.0 + 2.0 = 3.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(ONE_S, TWO_S, RoundMode.RNE)
expect(r.value).to_equal(THREE_S)
expect(r.flags).to_equal(0)
```

</details>

#### +0.0 + -0.0 = +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(POS_ZERO_S, NEG_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### +inf + finite = +inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(POS_INF_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
```

</details>

#### +inf + -inf = NaN (invalid)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(POS_INF_S, NEG_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### NaN + anything = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(QNAN_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FSUB.S

#### 3.0 - 1.0 = 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sub_s(THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(TWO_S)
```

</details>

#### 1.0 - 1.0 = +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sub_s(ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### +inf - +inf = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sub_s(POS_INF_S, POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FMUL.S

#### 2.0 * 3.0 = 6.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_s(TWO_S, THREE_S, RoundMode.RNE)
expect(r.value).to_equal(SIX_S)
```

</details>

#### 0.0 * inf = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_s(POS_ZERO_S, POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### -1.0 * 1.0 = -1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_s(NEG_ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(NEG_ONE_S)
```

</details>

#### any * NaN = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_s(TWO_S, QNAN_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FDIV.S

#### 6.0 / 2.0 = 3.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_s(SIX_S, TWO_S, RoundMode.RNE)
expect(r.value).to_equal(THREE_S)
```

</details>

#### 1.0 / 0.0 = +inf (divide by zero)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_s(ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
expect((r.flags and FP_FLAG_DZ) != 0).to_equal(true)
```

</details>

#### 0.0 / 0.0 = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_s(POS_ZERO_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### -1.0 / 0.0 = -inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_s(NEG_ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(NEG_INF_S)
```

</details>

### FSQRT.S

#### sqrt(4.0) = 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_s(FOUR_S, RoundMode.RNE)
expect(r.value).to_equal(TWO_S)
```

</details>

#### sqrt(0.0) = 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_s(POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### sqrt(-1.0) = NaN (invalid)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_s(NEG_ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### sqrt(+inf) = +inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_s(POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
