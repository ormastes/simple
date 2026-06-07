# RV64 Single-Precision FP Conversion Tests

> Unit tests for fcvt, fmv single-precision conversions.

<!-- sdn-diagram:id=rv64_fp_convert_s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_convert_s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_convert_s_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_convert_s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Conversion Tests

Unit tests for fcvt, fmv single-precision conversions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-CONVERT-S-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_convert_s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for fcvt, fmv single-precision conversions.

## Scenarios

### FCVT.W.S (float → i32)

#### 1.0 → 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_w_s(ONE_S, RoundMode.RTZ)
expect(r.value).to_equal(1)
```

</details>

#### -1.0 → -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_w_s(NEG_ONE_S, RoundMode.RTZ)
expect(r.value).to_equal(-1)
```

</details>

#### +inf → INT32_MAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_w_s(POS_INF_S, RoundMode.RTZ)
expect(r.value).to_equal(0x7FFFFFFF)
```

</details>

### FCVT.S.W (i32 → float)

#### 1 → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_w(1, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### -1 → -1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_w(-1, RoundMode.RNE)
expect(r.value).to_equal(NEG_ONE_S)
```

</details>

### FCVT.L.S (float → i64)

#### 1.0 → 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_l_s(ONE_S, RoundMode.RTZ)
expect(r.value).to_equal(1)
```

</details>

#### +inf → INT64_MAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_l_s(POS_INF_S, RoundMode.RTZ)
expect(r.value).to_equal(0x7FFFFFFFFFFFFFFF)
```

</details>

#### NaN → INT64_MAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_l_s(QNAN_S, RoundMode.RTZ)
expect(r.value).to_equal(0x7FFFFFFFFFFFFFFF)
```

</details>

### FCVT.S.L (i64 → float)

#### 1 → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_l(1, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### large value may be inexact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_l(0x7FFFFFFFFFFFFFFF, RoundMode.RNE)
expect((r.flags and 0x01) != 0).to_equal(true)
```

</details>

### FCVT.WU.S (float → u32)

#### 1.0 → 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_wu_s(ONE_S, RoundMode.RTZ)
expect(r.value).to_equal(1)
```

</details>

#### -1.0 → 0 (clamp)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_wu_s(NEG_ONE_S, RoundMode.RTZ)
expect(r.value).to_equal(0)
```

</details>

### FCVT.S.WU (u32 → float)

#### 1 → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_wu(1, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### 0xFFFFFFFF → large float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_wu(0xFFFFFFFF, RoundMode.RNE)
expect(r.value).to_be_greater_than(0)
```

</details>

### FCVT.LU.S / FCVT.S.LU

#### FCVT.LU.S: 1.0 → 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_lu_s(ONE_S, RoundMode.RTZ)
expect(r.value).to_equal(1)
```

</details>

#### FCVT.S.LU: 1 → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_lu(1, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

### FMV.X.W / FMV.W.X (bit copy)

#### FMV.X.W: copy float bits to integer (sign-extended)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fmv_x_w(NEG_ONE_S)
expect(result).to_equal(0xFFFFFFFFBF800000)
```

</details>

#### FMV.W.X: copy integer bits to float register

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fmv_w_x(ONE_S)
expect(result).to_equal(ONE_S)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
