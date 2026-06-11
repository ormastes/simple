# Dbfs Meta Store Facade Specification

> <details>

<!-- sdn-diagram:id=dbfs_meta_store_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_meta_store_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_meta_store_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_meta_store_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Meta Store Facade Specification

## Scenarios

### nogc_async_mut DBFS meta store facade

#### re-exports the hosted metadata journal backend

- var store = MetaStore create
   - Expected: store.write_inode(row) is true
   - Expected: entries.len() equals `1`
   - Expected: store.last_checkpoint_gen() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = MetaStore.create("/tmp/simple_dbfs_meta_facade_nogc")
val row = InodeRow(
    ino_id: 1, gen: 1, mode: 420,
    uid: 1000, gid: 1000, link_count: 1, size: 3,
    mtime: 1, ctime: 1, flags: 0
)
expect(store.write_inode(row)).to_equal(true)
val entries = store.replay_journal()
expect(entries.len()).to_equal(1)
expect(store.last_checkpoint_gen()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_meta_store_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut DBFS meta store facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
