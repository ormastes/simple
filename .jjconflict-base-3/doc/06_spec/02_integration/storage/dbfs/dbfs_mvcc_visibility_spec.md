# Dbfs Mvcc Visibility Specification

> <details>

<!-- sdn-diagram:id=dbfs_mvcc_visibility_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_mvcc_visibility_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_mvcc_visibility_spec -> std
dbfs_mvcc_visibility_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_mvcc_visibility_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Mvcc Visibility Specification

## Scenarios

### MvccHeader

#### creates with xmin set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = MvccHeader.create(10)
expect h.xmin == 10
expect h.xmax == 0
```

</details>

#### marks deleted with xmax

1. var h = MvccHeader create
2. h mark deleted


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = MvccHeader.create(10)
h.mark_deleted(20)
expect h.xmax == 20
```

</details>

### MvccTuple

#### creates tuple with data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = MvccTuple.create(5, "hello")
expect t.header.xmin == 5
expect t.data == "hello"
```

</details>

#### marks tuple deleted

1. var t = MvccTuple create
2. t delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = MvccTuple.create(5, "hello")
t.delete(10)
expect t.header.xmax == 10
```

</details>

### MvccSnapshot

#### detects active transactions

1. expect snap is txn active
2. expect snap is txn active
3. expect snap is txn active


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [3, 5, 7])
expect snap.is_txn_active(3) == true
expect snap.is_txn_active(5) == true
expect snap.is_txn_active(2) == false
```

</details>

### MVCC Visibility

#### committed insert is visible

1. expect mvcc is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tuple = MvccTuple.create(1, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == true
```

</details>

#### active insert is not visible

1. expect mvcc is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tuple = MvccTuple.create(5, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [5])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### future insert is not visible

1. expect mvcc is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tuple = MvccTuple.create(15, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### deleted tuple is not visible

1. var tuple = MvccTuple create
2. tuple delete
3. expect mvcc is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tuple = MvccTuple.create(1, "row1")
tuple.delete(5)
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### tuple deleted by active txn is still visible

1. var tuple = MvccTuple create
2. tuple delete
3. expect mvcc is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tuple = MvccTuple.create(1, "row1")
tuple.delete(5)
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [5])
expect mvcc_is_visible(tuple, snap) == true
```

</details>

### MvccTable

#### inserts and scans tuples

1. var table = MvccTable new
2. table insert
3. table insert
4. expect visible len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = MvccTable.new()
table.insert(1, "row1")
table.insert(1, "row2")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
val visible = table.scan(snap)
expect visible.len() == 2
```

</details>

#### counts visible tuples

1. var table = MvccTable new
2. table insert
3. table insert
4. table insert
5. expect table count visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = MvccTable.new()
table.insert(1, "a")
table.insert(1, "b")
table.insert(5, "c")
val snap = MvccSnapshot(xmin: 1, xmax: 4, active_txns: [])
expect table.count_visible(snap) == 2
```

</details>

#### delete hides tuple from scan

1. var table = MvccTable new
2. table insert
3. table insert
4. table delete matching
5. expect table count visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = MvccTable.new()
table.insert(1, "row1")
table.insert(1, "row2")
table.delete_matching(2, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect table.count_visible(snap) == 1
```

</details>

### MvccTxnManager

#### assigns incrementing txn ids

1. var mgr = MvccTxnManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
val h2 = mgr.begin()
expect h2.txn_id > h1.txn_id
```

</details>

#### tracks active transactions in snapshot

1. var mgr = MvccTxnManager new
2. expect snap is txn active
3. expect snap is txn active


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
val h2 = mgr.begin()
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == true
expect snap.is_txn_active(h2.txn_id) == true
```

</details>

#### commit removes from active

1. var mgr = MvccTxnManager new
2. mgr commit
3. expect snap is txn active
4. expect mgr get status


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
mgr.commit(h1.txn_id)
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == false
expect mgr.get_status(h1.txn_id) == "committed"
```

</details>

#### abort removes from active

1. var mgr = MvccTxnManager new
2. mgr abort
3. expect snap is txn active
4. expect mgr get status


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
mgr.abort(h1.txn_id)
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == false
expect mgr.get_status(h1.txn_id) == "aborted"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MvccHeader
- MvccTuple
- MvccSnapshot
- MVCC Visibility
- MvccTable
- MvccTxnManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
