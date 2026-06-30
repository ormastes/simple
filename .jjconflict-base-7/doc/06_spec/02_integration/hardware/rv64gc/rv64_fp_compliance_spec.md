# RV64 Floating-Point Compliance Integration Tests

> Comprehensive FP validation: IEEE 754 compliance, rounding modes, NaN handling.

<!-- sdn-diagram:id=rv64_fp_compliance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_compliance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_compliance_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_compliance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Floating-Point Compliance Integration Tests

Comprehensive FP validation: IEEE 754 compliance, rounding modes, NaN handling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-COMPLIANCE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/02_integration/hardware/rv64gc/rv64_fp_compliance_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive FP validation: IEEE 754 compliance, rounding modes, NaN handling.

## Scenarios

### F Extension Basic

#### fadd.s: 1+2=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(ONE_S, TWO_S, RoundMode.RNE)
expect(r.value).to_equal(THREE_S)
```

</details>

#### fmul.s: 1*1=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_s(ONE_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### fdiv.s: 1/0=inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_s(ONE_S, POS_ZERO_S, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_S)
```

</details>

#### NaN propagation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(QNAN_S, ONE_S, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
```

</details>

#### inf+(-inf)=NaN with NV flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(POS_INF_S, 0xFF800000, RoundMode.RNE)
expect(r.value).to_equal(QNAN_S)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

### D Extension Basic

#### fadd.d: 1+2=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(ONE_D, TWO_D, RoundMode.RNE)
expect(r.value).to_equal(THREE_D)
```

</details>

#### fmul.d: 1*1=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_mul_d(ONE_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### fdiv.d: 1/0=inf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_div_d(ONE_D, POS_ZERO_D, RoundMode.RNE)
expect(r.value).to_equal(POS_INF_D)
```

</details>

#### NaN propagation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(QNAN_D, ONE_D, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
```

</details>

#### inf+(-inf)=NaN with NV flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_d(POS_INF_D, 0xFFF0000000000000, RoundMode.RNE)
expect(r.value).to_equal(QNAN_D)
expect((r.flags and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

### F-D Conversion

#### fcvt.d.s: 1.0f → 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_d_s(ONE_S, RoundMode.RNE)
expect(r.value).to_equal(ONE_D)
```

</details>

#### fcvt.s.d: 1.0 → 1.0f

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fcvt_s_d(ONE_D, RoundMode.RNE)
expect(r.value).to_equal(ONE_S)
```

</details>

#### round-trip preserves value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = fcvt_d_s(ONE_S, RoundMode.RNE)
val s = fcvt_s_d(d.value, RoundMode.RNE)
expect(s.value).to_equal(ONE_S)
```

</details>

### Rounding Mode Effects

#### RNE and RTZ may differ for inexact results

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1.0/3.0 is inexact in single precision
val r_rne = fp_div_s(ONE_S, THREE_S, RoundMode.RNE)
val r_rtz = fp_div_s(ONE_S, THREE_S, RoundMode.RTZ)
# Both should set NX flag
expect((r_rne.flags and FP_FLAG_NX) != 0).to_equal(true)
expect((r_rtz.flags and FP_FLAG_NX) != 0).to_equal(true)
```

</details>

### Exception Flag Accumulation

#### multiple operations accumulate flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = fp_div_s(ONE_S, POS_ZERO_S, RoundMode.RNE)  # DZ
val r2 = fp_add_s(POS_INF_S, 0xFF800000, RoundMode.RNE)  # NV
val combined = r1.flags or r2.flags
expect((combined and FP_FLAG_DZ) != 0).to_equal(true)
expect((combined and FP_FLAG_NV) != 0).to_equal(true)
```

</details>

#### exact operations set no flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = fp_add_s(ONE_S, TWO_S, RoundMode.RNE)
expect(r.flags).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
