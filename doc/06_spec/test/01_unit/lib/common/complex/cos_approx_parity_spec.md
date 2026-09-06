# Cos Approx Parity Specification

> <details>

<!-- sdn-diagram:id=cos_approx_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cos_approx_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cos_approx_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cos_approx_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cos Approx Parity Specification

## Scenarios

### cos_approx canonical impl

#### Taylor-series correctness

#### cos(0) = 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = cos_approx(0.0)
expect r == 1.0
```

</details>

#### cos(PI) is approximately -1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = cos_approx(PI)
val diff = r - (0.0 - 1.0)
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
expect abs_diff < 0.000001
```

</details>

#### cos(PI/2) is approximately 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = cos_approx(PI / 2.0)
val abs_r = if r < 0.0: 0.0 - r else: r
expect abs_r < 0.000001
```

</details>

### sin_approx canonical impl

#### Taylor-series correctness

#### sin(0) = 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sin_approx(0.0)
expect r == 0.0
```

</details>

#### sin(PI/2) is approximately 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sin_approx(PI / 2.0)
val diff = r - 1.0
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
expect abs_diff < 0.000001
```

</details>

### Identity sin^2 + cos^2 = 1 (former-stub call sites are now real)

#### Pythagorean identity

#### holds at PI/4

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sin_approx(PI / 4.0)
val c = cos_approx(PI / 4.0)
val sum = s * s + c * c
val abs_diff = if sum > 1.0: sum - 1.0 else: 1.0 - sum
expect abs_diff < 0.000001
```

</details>

#### holds at PI/3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sin_approx(PI / 3.0)
val c = cos_approx(PI / 3.0)
val sum = s * s + c * c
val abs_diff = if sum > 1.0: sum - 1.0 else: 1.0 - sum
expect abs_diff < 0.000001
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/complex/cos_approx_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cos_approx canonical impl
- sin_approx canonical impl
- Identity sin^2 + cos^2 = 1 (former-stub call sites are now real)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
