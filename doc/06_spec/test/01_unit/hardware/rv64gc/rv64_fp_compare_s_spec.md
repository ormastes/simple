# RV64 Single-Precision FP Comparison Tests

> Unit tests for feq.s, flt.s, fle.s, fmin.s, fmax.s, fclass.s.

<!-- sdn-diagram:id=rv64_fp_compare_s_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_compare_s_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_compare_s_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_compare_s_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Single-Precision FP Comparison Tests

Unit tests for feq.s, flt.s, fle.s, fmin.s, fmax.s, fclass.s.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-COMPARE-S-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_compare_s_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for feq.s, flt.s, fle.s, fmin.s, fmax.s, fclass.s.

## Scenarios

### FEQ.S

#### equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_s(ONE_S, ONE_S)).to_equal(1)
```

</details>

#### unequal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_s(ONE_S, TWO_S)).to_equal(0)
```

</details>

#### +0.0 == -0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_s(POS_ZERO_S, NEG_ZERO_S)).to_equal(1)
```

</details>

#### NaN != NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_s(QNAN_S, QNAN_S)).to_equal(0)
```

</details>

### FLT.S

#### 1.0 < 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_s(ONE_S, TWO_S)).to_equal(1)
```

</details>

#### 2.0 not < 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_s(TWO_S, ONE_S)).to_equal(0)
```

</details>

#### equal not less

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_s(ONE_S, ONE_S)).to_equal(0)
```

</details>

#### -0.0 not < +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_s(NEG_ZERO_S, POS_ZERO_S)).to_equal(0)
```

</details>

#### NaN comparison returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_s(QNAN_S, ONE_S)).to_equal(0)
```

</details>

### FLE.S

#### 1.0 <= 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_s(ONE_S, TWO_S)).to_equal(1)
```

</details>

#### 1.0 <= 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_s(ONE_S, ONE_S)).to_equal(1)
```

</details>

#### 2.0 not <= 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_s(TWO_S, ONE_S)).to_equal(0)
```

</details>

#### -0.0 <= +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_s(NEG_ZERO_S, POS_ZERO_S)).to_equal(1)
```

</details>

### FMIN.S

#### min(1.0, 2.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_s(ONE_S, TWO_S)).to_equal(ONE_S)
```

</details>

#### min(2.0, 1.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_s(TWO_S, ONE_S)).to_equal(ONE_S)
```

</details>

#### min(-1.0, 1.0) = -1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_s(NEG_ONE_S, ONE_S)).to_equal(NEG_ONE_S)
```

</details>

#### min(NaN, 1.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_s(QNAN_S, ONE_S)).to_equal(ONE_S)
```

</details>

### FMAX.S

#### max(1.0, 2.0) = 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_s(ONE_S, TWO_S)).to_equal(TWO_S)
```

</details>

#### max(-1.0, 1.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_s(NEG_ONE_S, ONE_S)).to_equal(ONE_S)
```

</details>

#### max(NaN, 1.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_s(QNAN_S, ONE_S)).to_equal(ONE_S)
```

</details>

#### max(-0.0, +0.0) = +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_s(NEG_ZERO_S, POS_ZERO_S)).to_equal(POS_ZERO_S)
```

</details>

### FCLASS.S

#### -inf → bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(NEG_INF_S)).to_equal(1)
```

</details>

#### -normal → bit 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(NEG_ONE_S)).to_equal(2)
```

</details>

#### -subnormal → bit 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(NEG_SUBNORM_S)).to_equal(4)
```

</details>

#### -0 → bit 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(NEG_ZERO_S)).to_equal(8)
```

</details>

#### +0 → bit 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(POS_ZERO_S)).to_equal(16)
```

</details>

#### +subnormal → bit 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(POS_SUBNORM_S)).to_equal(32)
```

</details>

#### +normal → bit 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(ONE_S)).to_equal(64)
```

</details>

#### +inf → bit 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(POS_INF_S)).to_equal(128)
```

</details>

#### sNaN → bit 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(SNAN_S)).to_equal(256)
```

</details>

#### qNaN → bit 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_s(QNAN_S)).to_equal(512)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
