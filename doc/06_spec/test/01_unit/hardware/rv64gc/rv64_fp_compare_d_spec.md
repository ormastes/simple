# RV64 Double-Precision FP Comparison Tests

> Unit tests for feq.d, flt.d, fle.d, fmin.d, fmax.d, fclass.d.

<!-- sdn-diagram:id=rv64_fp_compare_d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_compare_d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_compare_d_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_compare_d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Double-Precision FP Comparison Tests

Unit tests for feq.d, flt.d, fle.d, fmin.d, fmax.d, fclass.d.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-COMPARE-D-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_compare_d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for feq.d, flt.d, fle.d, fmin.d, fmax.d, fclass.d.

## Scenarios

### FEQ.D

#### equal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_d(ONE_D, ONE_D)).to_equal(1)
```

</details>

#### unequal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_d(ONE_D, TWO_D)).to_equal(0)
```

</details>

#### +0.0 == -0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_d(POS_ZERO_D, NEG_ZERO_D)).to_equal(1)
```

</details>

#### NaN != NaN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_eq_d(QNAN_D, QNAN_D)).to_equal(0)
```

</details>

### FLT.D

#### 1.0 < 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_d(ONE_D, TWO_D)).to_equal(1)
```

</details>

#### 2.0 not < 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_d(TWO_D, ONE_D)).to_equal(0)
```

</details>

#### equal not less

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_d(ONE_D, ONE_D)).to_equal(0)
```

</details>

#### NaN comparison returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_d(QNAN_D, ONE_D)).to_equal(0)
```

</details>

#### -0.0 not < +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_lt_d(NEG_ZERO_D, POS_ZERO_D)).to_equal(0)
```

</details>

### FLE.D

#### 1.0 <= 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_d(ONE_D, TWO_D)).to_equal(1)
```

</details>

#### 1.0 <= 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_d(ONE_D, ONE_D)).to_equal(1)
```

</details>

#### 2.0 not <= 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_d(TWO_D, ONE_D)).to_equal(0)
```

</details>

#### -0.0 <= +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_le_d(NEG_ZERO_D, POS_ZERO_D)).to_equal(1)
```

</details>

### FMIN.D

#### min(1.0, 2.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_d(ONE_D, TWO_D)).to_equal(ONE_D)
```

</details>

#### min(-1.0, 1.0) = -1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_d(NEG_ONE_D, ONE_D)).to_equal(NEG_ONE_D)
```

</details>

#### min(NaN, 1.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_d(QNAN_D, ONE_D)).to_equal(ONE_D)
```

</details>

#### min(-0.0, +0.0) = -0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_min_d(NEG_ZERO_D, POS_ZERO_D)).to_equal(NEG_ZERO_D)
```

</details>

### FMAX.D

#### max(1.0, 2.0) = 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_d(ONE_D, TWO_D)).to_equal(TWO_D)
```

</details>

#### max(-1.0, 1.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_d(NEG_ONE_D, ONE_D)).to_equal(ONE_D)
```

</details>

#### max(NaN, 1.0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_d(QNAN_D, ONE_D)).to_equal(ONE_D)
```

</details>

#### max(-0.0, +0.0) = +0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_max_d(NEG_ZERO_D, POS_ZERO_D)).to_equal(POS_ZERO_D)
```

</details>

### FCLASS.D

#### -inf → bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(NEG_INF_D)).to_equal(1)
```

</details>

#### -normal → bit 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(NEG_ONE_D)).to_equal(2)
```

</details>

#### -subnormal → bit 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(NEG_SUBNORM_D)).to_equal(4)
```

</details>

#### -0 → bit 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(NEG_ZERO_D)).to_equal(8)
```

</details>

#### +0 → bit 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(POS_ZERO_D)).to_equal(16)
```

</details>

#### +subnormal → bit 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(POS_SUBNORM_D)).to_equal(32)
```

</details>

#### +normal → bit 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(ONE_D)).to_equal(64)
```

</details>

#### +inf → bit 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(POS_INF_D)).to_equal(128)
```

</details>

#### sNaN → bit 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(SNAN_D)).to_equal(256)
```

</details>

#### qNaN → bit 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fp_class_d(QNAN_D)).to_equal(512)
```

</details>

### FSGNJ.D / FSGNJN.D / FSGNJX.D

#### FSGNJ.D: copy sign positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ONE_D
val b = TWO_D
val result = (a and 0x7FFFFFFFFFFFFFFF) or (b and 0x8000000000000000)
expect(result).to_equal(ONE_D)
```

</details>

#### FSGNJ.D: copy sign negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ONE_D
val b = NEG_ONE_D
val result = (a and 0x7FFFFFFFFFFFFFFF) or (b and 0x8000000000000000)
expect(result).to_equal(NEG_ONE_D)
```

</details>

#### FSGNJN.D: negate sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ONE_D
val b = TWO_D
val sign_b = b and 0x8000000000000000
val neg_sign = sign_b xor 0x8000000000000000
val result = (a and 0x7FFFFFFFFFFFFFFF) or neg_sign
expect(result).to_equal(NEG_ONE_D)
```

</details>

#### FSGNJX.D: XOR signs positive+positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ONE_D
val b = TWO_D
val sign_xor = (a xor b) and 0x8000000000000000
val result = (a and 0x7FFFFFFFFFFFFFFF) or sign_xor
expect(result).to_equal(ONE_D)
```

</details>

#### FSGNJX.D: XOR signs positive+negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ONE_D
val b = NEG_ONE_D
val sign_xor = (a xor b) and 0x8000000000000000
val result = (a and 0x7FFFFFFFFFFFFFFF) or sign_xor
expect(result).to_equal(NEG_ONE_D)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
