# Seq Specification

> 1. nums = nums push

<!-- sdn-diagram:id=seq_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=seq_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

seq_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=seq_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Seq Specification

## Scenarios

### seq tool

#### single argument

#### generates 1 to N

1. nums = nums push
   - Expected: nums.len() equals `5`
   - Expected: nums[0] equals `1`
   - Expected: nums[4] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nums: [i64] = []
var i: i64 = 1
while i <= 5:
    nums = nums.push(i)
    i = i + 1
expect(nums.len()).to_equal(5)
expect(nums[0]).to_equal(1)
expect(nums[4]).to_equal(5)
```

</details>

#### two arguments

#### generates FIRST to LAST

1. nums = nums push
   - Expected: nums.len() equals `5`
   - Expected: nums[0] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nums: [i64] = []
var i: i64 = 3
while i <= 7:
    nums = nums.push(i)
    i = i + 1
expect(nums.len()).to_equal(5)
expect(nums[0]).to_equal(3)
```

</details>

#### three arguments

#### generates with increment

1. nums = nums push
   - Expected: nums.len() equals `6`
   - Expected: nums[0] equals `0`
   - Expected: nums[5] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nums: [i64] = []
var i: i64 = 0
while i <= 10:
    nums = nums.push(i)
    i = i + 2
expect(nums.len()).to_equal(6)
expect(nums[0]).to_equal(0)
expect(nums[5]).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/seq_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- seq tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
