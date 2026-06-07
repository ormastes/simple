# Map Insert If Absent Specification

> 1. var map: Map<text, i32> = Map new

<!-- sdn-diagram:id=map_insert_if_absent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=map_insert_if_absent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

map_insert_if_absent_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=map_insert_if_absent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map Insert If Absent Specification

## Scenarios

### nogc_async_mut pure Map insert_if_absent

#### inserts missing keys without overwriting existing values

1. var map: Map<text, i32> = Map new
   - Expected: map.insert_if_absent("name", 1) is true
   - Expected: map.len() equals `1`
   - Expected: map.get("name")? equals `1`
   - Expected: map.insert_if_absent("name", 2) is false
   - Expected: map.len() equals `1`
   - Expected: map.get("name")? equals `1`
   - Expected: map.insert_if_absent("other", 3) is true
   - Expected: map.len() equals `2`
   - Expected: map.get("other")? equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map: Map<text, i32> = Map.new()

expect(map.insert_if_absent("name", 1)).to_equal(true)
expect(map.len()).to_equal(1)
expect(map.get("name")?).to_equal(1)

expect(map.insert_if_absent("name", 2)).to_equal(false)
expect(map.len()).to_equal(1)
expect(map.get("name")?).to_equal(1)

expect(map.insert_if_absent("other", 3)).to_equal(true)
expect(map.len()).to_equal(2)
expect(map.get("other")?).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/map_insert_if_absent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut pure Map insert_if_absent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
