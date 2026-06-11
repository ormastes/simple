# Dbfs Dentry Prefix Index Specification

> 1. table insert

<!-- sdn-diagram:id=dbfs_dentry_prefix_index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_dentry_prefix_index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_dentry_prefix_index_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_dentry_prefix_index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Dentry Prefix Index Specification

## Scenarios

### DBFS dentry prefix index

#### finds exact children through the shared prefix index

1. table insert
2. table insert
   - Expected: found.child_ino equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = DentryTable.new()
table.insert(DentryRow(parent_ino: 1, name: "src", child_ino: 10, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 2, name: "src", child_ino: 20, gen: 0)).unwrap()

val found = table.find_child_accel(2, "src").unwrap()

expect(found.child_ino).to_equal(20)
```

</details>

#### lists only matching children for the requested parent and prefix

1. table insert
2. table insert
3. table insert
4. table insert
   - Expected: rows.len() equals `2`
   - Expected: rows[0].child_ino equals `1`
   - Expected: rows[1].child_ino equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = DentryTable.new()
table.insert(DentryRow(parent_ino: 7, name: "src_main", child_ino: 1, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 7, name: "src_test", child_ino: 2, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 7, name: "doc_readme", child_ino: 3, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 8, name: "src_other_parent", child_ino: 4, gen: 0)).unwrap()

val rows = table.list_children_with_prefix(7, "src")

expect(rows.len()).to_equal(2)
expect(rows[0].child_ino).to_equal(1)
expect(rows[1].child_ino).to_equal(2)
```

</details>

#### rebuilds the index after removal so stale row positions are not returned

1. table insert
2. table insert
3. table insert
4. table remove
   - Expected: rows.len() equals `2`
   - Expected: rows[0].child_ino equals `12`
   - Expected: rows[1].child_ino equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = DentryTable.new()
table.insert(DentryRow(parent_ino: 1, name: "alpha", child_ino: 11, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 1, name: "beta", child_ino: 12, gen: 0)).unwrap()
table.insert(DentryRow(parent_ino: 1, name: "bravo", child_ino: 13, gen: 0)).unwrap()

table.remove(DentryKey(parent_ino: 1, name: "alpha")).unwrap()
val rows = table.list_children_with_prefix(1, "b")

expect(rows.len()).to_equal(2)
expect(rows[0].child_ino).to_equal(12)
expect(rows[1].child_ino).to_equal(13)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db/dbfs_dentry_prefix_index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DBFS dentry prefix index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
