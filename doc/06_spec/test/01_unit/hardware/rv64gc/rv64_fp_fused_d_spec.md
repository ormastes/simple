# RV64 Double-Precision FP Fused Multiply-Add Tests

> Unit tests for fmadd.d, fmsub.d, fnmadd.d, fnmsub.d.

<!-- sdn-diagram:id=rv64_fp_fused_d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_fused_d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_fused_d_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_fused_d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Double-Precision FP Fused Multiply-Add Tests

Unit tests for fmadd.d, fmsub.d, fnmadd.d, fnmsub.d.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-FUSED-D-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_fused_d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for fmadd.d, fmsub.d, fnmadd.d, fnmsub.d.

## Scenarios

### FMADD.D (a*b+c)

#### 2*3+1 = 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(SEVEN_D)
```

</details>

#### 1*1+0 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_d(ONE_D, ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### inf*0+1 = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_d(POS_INF_D, POS_ZERO_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### NaN propagates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_d(QNAN_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FMSUB.D (a*b-c)

#### 2*3-1 = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmsub_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(FIVE_D)
```

</details>

#### 1*1-1 = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmsub_d(ONE_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### inf*1-inf = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmsub_d(POS_INF_D, ONE_D, POS_INF_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FNMADD.D (-(a*b)-c)

#### -(2*3)-1 = -7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmadd_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_SEVEN_D)
```

</details>

#### NaN propagates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmadd_d(QNAN_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

### FNMSUB.D (-(a*b)+c)

#### -(2*3)+1 = -5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmsub_d(TWO_D, THREE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(NEG_FIVE_D)
```

</details>

#### -(1*1)+1 = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmsub_d(ONE_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_D)
```

</details>

#### NaN propagates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmsub_d(QNAN_D, ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
