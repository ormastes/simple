# RV64 Double-Precision FP Conversion Tests

> Unit tests for double-precision conversions: fcvt.d.s, fcvt.s.d, fcvt.w.d, etc.

<!-- sdn-diagram:id=rv64_fp_convert_d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_convert_d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_convert_d_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_convert_d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Double-Precision FP Conversion Tests

Unit tests for double-precision conversions: fcvt.d.s, fcvt.s.d, fcvt.w.d, etc.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-CONVERT-D-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_convert_d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for double-precision conversions: fcvt.d.s, fcvt.s.d, fcvt.w.d, etc.

## Scenarios

### FCVT.D.S (single → double)

#### 1.0f → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_s(ONE_S, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### conversion is exact (no precision loss)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_s(ONE_S, RoundMode.RNE)
expect(r.flags).to_equal(0)
```

</details>

#### NaN converts to double NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_s(0x7FC00000, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FCVT.S.D (double → single)

#### 1.0 → 1.0f

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_d(ONE_D, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### large double may lose precision

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_d(0x7FEFFFFFFFFFFFFF, RoundMode.RNE)
expect((r.flags and 0x01) != 0).to_equal(true)
```

</details>

### FCVT.W.D (double → i32)

#### 1.0 → 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_w_d(ONE_D, RoundMode.RTZ)
expect(r.value).to_equal(1)
```

</details>

#### -1.0 → -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_w_d(NEG_ONE_D, RoundMode.RTZ)
expect(r.value).to_equal(-1)
```

</details>

#### +inf → INT32_MAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_w_d(POS_INF_D, RoundMode.RTZ)
expect(r.value).to_equal(0x7FFFFFFF)
```

</details>

### FCVT.D.W (i32 → double)

#### 1 → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_w(1, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### -1 → -1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_w(-1, RoundMode.RNE)
expect(r.value).to_equal(NEG_ONE_D)
```

</details>

### FCVT.L.D (double → i64)

#### 1.0 → 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_l_d(ONE_D, RoundMode.RTZ)
expect(r.value).to_equal(1)
```

</details>

#### NaN → INT64_MAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_l_d(QNAN_D, RoundMode.RTZ)
expect(r.value).to_equal(0x7FFFFFFFFFFFFFFF)
```

</details>

#### +inf → INT64_MAX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_l_d(POS_INF_D, RoundMode.RTZ)
expect(r.value).to_equal(0x7FFFFFFFFFFFFFFF)
```

</details>

### FCVT.D.L (i64 → double)

#### 1 → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_l(1, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### large i64 may be inexact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_l(0x7FFFFFFFFFFFFFFF, RoundMode.RNE)
expect((r.flags and 0x01) != 0).to_equal(true)
```

</details>

### FMV.X.D / FMV.D.X (bit copy)

#### FMV.X.D: copy double bits to integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fmv_x_d(ONE_D)
expect(result).to_equal(ONE_D)
```

</details>

#### FMV.D.X: copy integer bits to double register

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fmv_d_x(ONE_D)
expect(result).to_equal(ONE_D)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
