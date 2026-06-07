# Map Traversal Specification

> 1. var map: Map<i64, i64> = Map new

<!-- sdn-diagram:id=map_traversal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=map_traversal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

map_traversal_spec -> std
map_traversal_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=map_traversal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Map Traversal Specification

## Scenarios

### nogc_sync_mut Map traversal helpers

#### filters entries without changing source map

1. var map: Map<i64, i64> = Map new
2. map insert
3. map insert
4. map insert
5. expect filtered has
6. expect filtered get
7. expect filtered get
8. expect map len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map: Map<i64, i64> = Map.new()
map.insert(1, 1)
map.insert(2, 2)
map.insert(3, 3)

val filtered = map.filter(\key, value: value >= 2)

expect filtered.has(1) to_equal false
expect filtered.get(2).unwrap() to_equal 2
expect filtered.get(3).unwrap() to_equal 3
expect map.len() to_equal 3
```

</details>

#### maps values while preserving keys

1. var map: Map<i64, i64> = Map new
2. map insert
3. map insert
4. expect mapped get
5. expect mapped get
6. expect map get


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map: Map<i64, i64> = Map.new()
map.insert(1, 4)
map.insert(2, 7)

val mapped = map.map_values(_1 * 10)

expect mapped.get(1).unwrap() to_equal 40
expect mapped.get(2).unwrap() to_equal 70
expect map.get(1).unwrap() to_equal 4
```

</details>

#### visits each entry exactly once

1. var map: Map<i64, i64> = Map new
2. map insert
3. map insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map: Map<i64, i64> = Map.new()
map.insert(1, 1)
map.insert(2, 2)
var total = 0
var count = 0

map.for_each(\key, value:
    total = total + value
    count = count + 1
)

expect total to_equal 3
expect count to_equal 2
```

</details>

#### merges entries from another map

1. var left: Map<i64, i64> = Map new
2. left insert
3. left insert
4. var right: Map<i64, i64> = Map new
5. right insert
6. right insert
7. left merge
8. expect left get
9. expect left get
10. expect left get
11. expect left len


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var left: Map<i64, i64> = Map.new()
left.insert(1, 1)
left.insert(2, 2)
var right: Map<i64, i64> = Map.new()
right.insert(2, 20)
right.insert(3, 30)

left.merge(right)

expect left.get(1).unwrap() to_equal 1
expect left.get(2).unwrap() to_equal 20
expect left.get(3).unwrap() to_equal 30
expect left.len() to_equal 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/map_traversal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_sync_mut Map traversal helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
