# Dbfs Schema Facade Specification

> <details>

<!-- sdn-diagram:id=dbfs_schema_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_schema_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_schema_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_schema_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Schema Facade Specification

## Scenarios

### gc_async_mut DBFS schema facade

#### re-exports schema tables and file metadata helpers

- var inodes = InodeTable new
- var dentries = DentryTable new
   - Expected: inodes.insert(root).is_ok() is true
   - Expected: inodes.insert(file).is_ok() is true
   - Expected: dentries.insert(DentryRow(parent_ino: 1, name: "hello.txt", child_ino: 2, gen: 1)).is_ok() is true
   - Expected: inodes.get(InodeKey(ino_id: 2)).unwrap().size equals `5`
   - Expected: dentries.get(DentryKey(parent_ino: 1, name: "hello.txt")).unwrap().child_ino equals `2`
   - Expected: meta.is_file is true
   - Expected: check_read(meta, 1000, 1000) is true
   - Expected: check_write(meta, 1000, 1000) is true
   - Expected: check_exec(meta, 1000, 1000) is false
- var cache = InodeHintsCache new
   - Expected: resolved.is_ok() is true
   - Expected: resolved.unwrap().ino_id equals `2`
   - Expected: batch_stat(1, "/", dentries, inodes).len() equals `1`
   - Expected: PERM_READ != PERM_WRITE is true
   - Expected: PERM_EXEC < PERM_READ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var inodes = InodeTable.new()
var dentries = DentryTable.new()
val root = InodeRow(
    ino_id: 1, gen: 1, mode: S_IFDIR | 493,
    uid: 1000, gid: 1000, link_count: 2, size: 0,
    mtime: 10, ctime: 10, flags: 0
)
val file = InodeRow(
    ino_id: 2, gen: 1, mode: S_IFREG | 420,
    uid: 1000, gid: 1000, link_count: 1, size: 5,
    mtime: 20, ctime: 20, flags: 0
)
expect(inodes.insert(root).is_ok()).to_equal(true)
expect(inodes.insert(file).is_ok()).to_equal(true)
expect(dentries.insert(DentryRow(parent_ino: 1, name: "hello.txt", child_ino: 2, gen: 1)).is_ok()).to_equal(true)
expect(inodes.get(InodeKey(ino_id: 2)).unwrap().size).to_equal(5)
expect(dentries.get(DentryKey(parent_ino: 1, name: "hello.txt")).unwrap().child_ino).to_equal(2)

val meta = file_meta_from_inode(file, "/hello.txt", "hello.txt", 1)
expect(meta.is_file).to_equal(true)
expect(check_read(meta, 1000, 1000)).to_equal(true)
expect(check_write(meta, 1000, 1000)).to_equal(true)
expect(check_exec(meta, 1000, 1000)).to_equal(false)

var cache = InodeHintsCache.new(8)
val resolved = resolve_path("/hello.txt", dentries, inodes, cache)
expect(resolved.is_ok()).to_equal(true)
expect(resolved.unwrap().ino_id).to_equal(2)
expect(batch_stat(1, "/", dentries, inodes).len()).to_equal(1)
expect(PERM_READ != PERM_WRITE).to_equal(true)
expect(PERM_EXEC < PERM_READ).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut DBFS schema facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
