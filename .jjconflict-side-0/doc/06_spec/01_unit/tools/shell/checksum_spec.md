# Checksum Specification

> 1. hash1 =

<!-- sdn-diagram:id=checksum_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=checksum_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

checksum_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=checksum_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Checksum Specification

## Scenarios

### checksum tool

#### hash computation

#### produces consistent hash for same input

1. hash1 =
2. hash2 =
   - Expected: hash1 equals `hash2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "hello"
var hash1: u64 = 5381
var hash2: u64 = 5381
for ch in input:
    hash1 = ((hash1 << 5) + hash1) + ch.to_i32()
    hash2 = ((hash2 << 5) + hash2) + ch.to_i32()
expect(hash1).to_equal(hash2)
```

</details>

#### produces different hash for different input

1. h1 =
2. h2 =
   - Expected: h1 != h2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h1: u64 = 5381
var h2: u64 = 5381
for ch in "hello":
    h1 = ((h1 << 5) + h1) + ch.to_i32()
for ch in "world":
    h2 = ((h2 << 5) + h2) + ch.to_i32()
expect(h1 != h2).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/checksum_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- checksum tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
