# Probability Utilities Specification

> This specification covers basic probability calculation utilities: 1. Collision probability (birthday paradox) 2. Hash collision estimation

<!-- sdn-diagram:id=probability_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=probability_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

probability_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=probability_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Probability Utilities Specification

This specification covers basic probability calculation utilities: 1. Collision probability (birthday paradox) 2. Hash collision estimation

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PROB-001 to #PROB-004 |
| Category | Tooling \| Probability & Statistics |
| Difficulty | 1/5 |
| Status | Complete |
| Source | `test/01_unit/app/tooling/probability_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification covers basic probability calculation utilities:
1. Collision probability (birthday paradox)
2. Hash collision estimation

## Key Concepts

| Concept | Description |
|---------|-------------|
| Birthday Paradox | Probability of collisions in large hash spaces |
| Collision Probability | Likelihood of hash collision for n items |
| Hash Space | Total number of possible hash values (2^64) |

## Behavior

- Returns 0.0 for n ≤ 0
- Returns 0.0 for n = 1 (can't collide with nothing)
- Probability increases quadratically with n
- Uses simplified birthday paradox formula for 64-bit hashes

## Scenarios

### Probability Utilities

### Collision Probability

#### returns 0 for n=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prob = collision_probability(0)
expect prob == 0.0
```

</details>

#### returns very low probability for small n

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prob = collision_probability(10)
expect prob < 0.0001
```

</details>

#### returns low probability for moderate n

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prob = collision_probability(1000)
expect prob < 0.01
```

</details>

#### probability increases with n

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prob_10 = collision_probability(10)
val prob_100 = collision_probability(100)
expect prob_100 > prob_10
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
