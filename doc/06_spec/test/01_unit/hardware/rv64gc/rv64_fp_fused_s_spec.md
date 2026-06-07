# RV64 Single-Precision FP Fused Multiply-Add Tests

> Unit tests for fmadd.s, fmsub.s, fnmadd.s, fnmsub.s.

<!-- sdn-diagram:id=rv64_fp_fused_s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_fused_s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_fused_s_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_fused_s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Fused Multiply-Add Tests

Unit tests for fmadd.s, fmsub.s, fnmadd.s, fnmsub.s.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-FUSED-S-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_fused_s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for fmadd.s, fmsub.s, fnmadd.s, fnmsub.s.

## Scenarios

### FMADD.S (a*b+c)

#### 2*3+1 = 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(SEVEN_S)
```

</details>

#### 1*1+0 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_s(ONE_S, ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### inf*0+1 = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_s(POS_INF_S, POS_ZERO_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

#### NaN propagates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmadd_s(QNAN_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FMSUB.S (a*b-c)

#### 2*3-1 = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmsub_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(FIVE_S)
```

</details>

#### 1*1-1 = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmsub_s(ONE_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### inf*1-inf = NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fmsub_s(POS_INF_S, ONE_S, POS_INF_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FNMADD.S (-(a*b)+c) [NOTE: actually -(a*b)-c per spec]

#### -(2*3)-1 = -7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmadd_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(0xC0E00000)
```

</details>

#### NaN propagates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmadd_s(QNAN_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

### FNMSUB.S (-(a*b)+c)

#### -(2*3)+1 = -5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmsub_s(TWO_S, THREE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(0xC0A00000)
```

</details>

#### -(1*1)+1 = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmsub_s(ONE_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(POS_ZERO_S)
```

</details>

#### NaN propagates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_fnmsub_s(QNAN_S, ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
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
