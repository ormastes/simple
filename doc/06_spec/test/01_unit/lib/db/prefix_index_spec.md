# Prefix Index Specification

> 1. var idx = prefix index new

<!-- sdn-diagram:id=prefix_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=prefix_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

prefix_index_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=prefix_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Prefix Index Specification

## Scenarios

### DB prefix index

#### supports exact and prefix lookup on unsorted inserts

1. var idx = prefix index new
2. idx = prefix index insert
3. idx = prefix index insert
4. idx = prefix index insert
   - Expected: exact.len() equals `1`
   - Expected: exact[0] equals `10`
   - Expected: prefix.len() equals `2`
   - Expected: prefix[0] equals `10`
   - Expected: prefix[1] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = prefix_index_new()
idx = prefix_index_insert(idx, "tenant/b/order/2", 20)
idx = prefix_index_insert(idx, "tenant/a/order/1", 10)
idx = prefix_index_insert(idx, "tenant/a/order/3", 30)

val exact = prefix_index_lookup_exact(idx, "tenant/a/order/1")
val prefix = prefix_index_lookup_prefix(idx, "tenant/a/")

expect(exact.len()).to_equal(1)
expect(exact[0]).to_equal(10)
expect(prefix.len()).to_equal(2)
expect(prefix[0]).to_equal(10)
expect(prefix[1]).to_equal(30)
```

</details>

#### reports a sorted prefix range for repeated scans

1. var idx = prefix index new
2. idx = prefix index insert
3. idx = prefix index insert
4. idx = prefix index insert
   - Expected: range.start equals `0`
   - Expected: range.end equals `2`
   - Expected: range.matched_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = prefix_index_new()
idx = prefix_index_insert(idx, "sys/b", 2)
idx = prefix_index_insert(idx, "app/a", 1)
idx = prefix_index_insert(idx, "app/b", 3)
val sorted = prefix_index_sort(idx)

val range = prefix_index_prefix_range(sorted, "app/")

expect(range.start).to_equal(0)
expect(range.end).to_equal(2)
expect(range.matched_count).to_equal(2)
```

</details>

#### supports hierarchical descendant lookups with exact root inclusion

1. var idx = prefix index new
2. idx = prefix index insert
3. idx = prefix index insert
4. idx = prefix index insert
5. idx = prefix index insert
   - Expected: hits.len() equals `3`
   - Expected: hits[0] equals `1`
   - Expected: hits[1] equals `2`
   - Expected: hits[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = prefix_index_new()
idx = prefix_index_insert(idx, "cfg", 1)
idx = prefix_index_insert(idx, "cfg/db/host", 2)
idx = prefix_index_insert(idx, "cfg/db/port", 3)
idx = prefix_index_insert(idx, "cfgx/db/host", 4)

val hits = prefix_index_lookup_descendants(idx, "cfg")

expect(hits.len()).to_equal(3)
expect(hits[0]).to_equal(1)
expect(hits[1]).to_equal(2)
expect(hits[2]).to_equal(3)
```

</details>

#### is used by DbTable prefix scans after index rebuild

1. table insert
2. table insert
3. table insert
   - Expected: result.count equals `2`
   - Expected: result.ids[0] equals `2`
   - Expected: result.ids[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = db_table_new("kv")
table.insert("user/002", "b")
table.insert("admin/001", "root")
table.insert("user/001", "a")

val result = db_table_prefix_scan(table, "user/")

expect(result.count).to_equal(2)
expect(result.ids[0]).to_equal(2)
expect(result.ids[1]).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/prefix_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DB prefix index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
