# Limb Spike Specification

> <details>

<!-- sdn-diagram:id=limb_spike_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=limb_spike_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

limb_spike_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=limb_spike_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Limb Spike Specification

## Scenarios

### math.bignum.limb

### limb_mul

#### LIMB_MASK^2 = (1, LIMB_BASE - 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# (2^30 - 1)^2 = 2^60 - 2^31 + 1
#              = (2^30 - 2) * 2^30 + 1
# so low limb = 1, high limb = LIMB_BASE - 2.
val r = limb_mul(LIMB_MASK, LIMB_MASK)
expect(r[0]).to_equal(1)
expect(r[1]).to_equal(LIMB_BASE - 2)
```

</details>

### add_limbs

#### carries at LIMB_BASE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LIMB_MASK + 1 = LIMB_BASE -> carry out, limb 0.
val r = add_limbs(LIMB_MASK, 1, 0)
expect(r[0]).to_equal(0)
expect(r[1]).to_equal(1)
```

</details>

### sub_limbs

#### borrows when a < b

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0 - 1 = LIMB_MASK with borrow_out 1.
val r = sub_limbs(0, 1, 0)
expect(r[0]).to_equal(LIMB_MASK)
expect(r[1]).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/math/bignum/limb_spike_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- math.bignum.limb
- limb_mul
- add_limbs
- sub_limbs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
