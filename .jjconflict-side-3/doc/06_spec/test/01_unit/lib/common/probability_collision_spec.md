# Probability Collision Specification

> <details>

<!-- sdn-diagram:id=probability_collision_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=probability_collision_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

probability_collision_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=probability_collision_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Probability Collision Specification

## Scenarios

### collision_probability

#### returns 0 for n=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collision_probability(0)
expect(result).to_equal(0.0)
```

</details>

#### returns 0 for n=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collision_probability(1)
expect(result).to_equal(0.0)
```

</details>

#### returns 0 for negative n

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collision_probability(-5)
expect(result).to_equal(0.0)
```

</details>

#### returns positive probability for n=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collision_probability(2)
val positive = result > 0.0
expect(positive).to_equal(true)
```

</details>

#### returns very small probability for n=10

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collision_probability(10)
val very_small = result < 0.001
val positive = result > 0.0
expect(very_small).to_equal(true)
expect(positive).to_equal(true)
```

</details>

#### probability increases with n

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p10 = collision_probability(10)
val p100 = collision_probability(100)
val p1000 = collision_probability(1000)
val p10_lt_p100 = p10 < p100
val p100_lt_p1000 = p100 < p1000
expect(p10_lt_p100).to_equal(true)
expect(p100_lt_p1000).to_equal(true)
```

</details>

#### probability for n=1000 is still very small (64-bit space)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collision_probability(1000)
val tiny = result < 0.001
expect(tiny).to_equal(true)
```

</details>

#### probability scales quadratically with n

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P(n) ~ n*(n-1) / (2 * 2^64)
# P(2n) ~ 4 * P(n) for small n
val p100 = collision_probability(100)
val p200 = collision_probability(200)
# ratio should be approximately 4 (actually about (200*199)/(100*99) ~ 3.98)
val ratio = p200 / p100
val near_4 = ratio > 3.5
val under_5 = ratio < 4.5
expect(near_4).to_equal(true)
expect(under_5).to_equal(true)
```

</details>

#### returns non-negative probability for large n

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = collision_probability(100000)
val non_neg = result >= 0.0
expect(non_neg).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/probability_collision_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- collision_probability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
