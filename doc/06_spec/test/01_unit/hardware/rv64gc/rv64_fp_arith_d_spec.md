# RV64 Double-Precision FP Arithmetic Tests

> Unit tests for double-precision FP: fadd.d, fsub.d, fmul.d, fdiv.d, fsqrt.d.

<!-- sdn-diagram:id=rv64_fp_arith_d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_arith_d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_arith_d_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_arith_d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Double-Precision FP Arithmetic Tests

Unit tests for double-precision FP: fadd.d, fsub.d, fmul.d, fdiv.d, fsqrt.d.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-ARITH-D-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_arith_d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for double-precision FP: fadd.d, fsub.d, fmul.d, fdiv.d, fsqrt.d.

## Scenarios

### FADD.D

#### 1.0 + 2.0 = 3.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(ONE_D, TWO_D, RoundMode.RNE)
expect(r.value).to_equal(THREE_D)
```

</details>

#### +0.0 + -0.0 = +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(POS_ZERO_D, NEG_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### +inf + -inf = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(POS_INF_D, NEG_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### +inf + finite = +inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(POS_INF_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
```

</details>

#### NaN + anything = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(QNAN_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FSUB.D

#### 3.0 - 1.0 = 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sub_d(THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(TWO_D)
```

</details>

#### 1.0 - 1.0 = +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sub_d(ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### +inf - +inf = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sub_d(POS_INF_D, POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FMUL.D

#### 2.0 * 3.0 = 6.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_d(TWO_D, THREE_D, RoundMode.RNE)
expect(r.value).to_equal(SIX_D)
```

</details>

#### 0.0 * inf = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_d(POS_ZERO_D, POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### -1.0 * 1.0 = -1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_d(NEG_ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_ONE_D)
```

</details>

#### any * NaN = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_d(TWO_D, QNAN_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FDIV.D

#### 6.0 / 2.0 = 3.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_d(SIX_D, TWO_D, RoundMode.RNE)
expect(r.value).to_equal(THREE_D)
```

</details>

#### 1.0 / 0.0 = +inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_d(ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
expect((r.flags and FP_FLAG_DZ) != 0).to_equal(true)
```

</details>

#### 0.0 / 0.0 = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_d(POS_ZERO_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### -1.0 / 0.0 = -inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_d(NEG_ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_INF_D)
```

</details>

### FSQRT.D

#### sqrt(4.0) = 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_d(FOUR_D, RoundMode.RNE)
expect(r.value).to_equal(TWO_D)
```

</details>

#### sqrt(0.0) = 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_d(POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### sqrt(-1.0) = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_d(NEG_ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### sqrt(+inf) = +inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_sqrt_d(POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
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
