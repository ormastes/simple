# Hashset Probe Specification

> 1. var set = hashset with capacity

<!-- sdn-diagram:id=hashset_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hashset_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hashset_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hashset_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hashset Probe Specification

## Scenarios

### nogc_sync_mut HashSet

#### preserves membership after removal from preallocated table

1. var set = hashset with capacity
2. set insert
3. set insert
4. set insert
   - Expected: set.remove("beta") is true
   - Expected: set contains `alpha`
   - Expected: set does not contain `beta`
   - Expected: set contains `gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = hashset_with_capacity(3)
set.insert("alpha")
set.insert("beta")
set.insert("gamma")

expect(set.remove("beta")).to_equal(true)
expect(set.contains("alpha")).to_equal(true)
expect(set.contains("beta")).to_equal(false)
expect(set.contains("gamma")).to_equal(true)
```

</details>

#### deduplicates and probes across a resized table

1. var set = hashset with capacity
   - Expected: set.insert("one") is true
   - Expected: set.insert("two") is true
   - Expected: set.insert("three") is true
   - Expected: set.insert("two") is false
   - Expected: set.len() equals `3`
   - Expected: set contains `one`
   - Expected: set contains `two`
   - Expected: set contains `three`
   - Expected: set does not contain `missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = hashset_with_capacity(2)
expect(set.insert("one")).to_equal(true)
expect(set.insert("two")).to_equal(true)
expect(set.insert("three")).to_equal(true)
expect(set.insert("two")).to_equal(false)

expect(set.len()).to_equal(3)
expect(set.contains("one")).to_equal(true)
expect(set.contains("two")).to_equal(true)
expect(set.contains("three")).to_equal(true)
expect(set.contains("missing")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/hashset_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_sync_mut HashSet

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
