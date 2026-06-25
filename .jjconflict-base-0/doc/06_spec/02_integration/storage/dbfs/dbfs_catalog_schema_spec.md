# dbfs_catalog_schema_spec

> DBFS Catalog Schema Specification

<!-- sdn-diagram:id=dbfs_catalog_schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_catalog_schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_catalog_schema_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_catalog_schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_catalog_schema_spec

DBFS Catalog Schema Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_catalog_schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Catalog Schema Specification

Verifies all 11 D3 tables have correct key shapes and round-trip
through the pager:
  INODE, DENTRY, FILE_VERSION, EXTENT_REF, EXTENT, BLOCK_BLOB,
  XATTR, ACL_ENTRY, TXN, WAL_RECORD, STORAGE_CLASS

## Scenarios

### DBFS Schema — INODE table

#### INODE key is ino_id only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = InodeKey(ino_id: 42)
expect(key.ino_id).to_equal(42)
```

</details>

#### INODE row round-trips through pager

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = InodeRow(ino_id: 1, gen: 0, mode: 0o644, uid: 0, gid: 0,
                   link_count: 1, size: 0, mtime: 0, ctime: 0, flags: 0)
val tbl = SchemaTable.inode()
val id = tbl.insert(row).unwrap()
val got = tbl.get(InodeKey(ino_id: 1)).unwrap()
expect(got.ino_id).to_equal(1)
```

</details>

### DBFS Schema — DENTRY table

#### DENTRY key is (parent_ino, name)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = DentryKey(parent_ino: 1, name: "foo")
expect(key.parent_ino).to_equal(1)
expect(key.name).to_equal("foo")
```

</details>

#### DENTRY row round-trips through pager

1. tbl insert
   - Expected: got.child_ino equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.dentry()
val row = DentryRow(parent_ino: 1, name: "bar", child_ino: 2, gen: 0)
tbl.insert(row).unwrap()
val got = tbl.get(DentryKey(parent_ino: 1, name: "bar")).unwrap()
expect(got.child_ino).to_equal(2)
```

</details>

#### accelerated name lookup remains correct across summary-hash collisions

1. tbl insert
2. tbl insert
   - Expected: got.child_ino equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.dentry()
tbl.insert(DentryRow(parent_ino: 9, name: "ab", child_ino: 10, gen: 0)).unwrap()
tbl.insert(DentryRow(parent_ino: 9, name: "ba", child_ino: 11, gen: 0)).unwrap()

val got = tbl.find_child_accel(9, "ba").unwrap()
expect(got.child_ino).to_equal(11)
```

</details>

#### accelerated prefix scan returns only matching children

1. tbl insert
2. tbl insert
3. tbl insert
   - Expected: rows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.dentry()
tbl.insert(DentryRow(parent_ino: 3, name: "src_main", child_ino: 1, gen: 0)).unwrap()
tbl.insert(DentryRow(parent_ino: 3, name: "src_test", child_ino: 2, gen: 0)).unwrap()
tbl.insert(DentryRow(parent_ino: 3, name: "doc_readme", child_ino: 3, gen: 0)).unwrap()

val rows = tbl.list_children_with_prefix(3, "src")
expect(rows.len()).to_equal(2)
```

</details>

### DBFS Schema — FILE_VERSION table

#### FILE_VERSION key is (ino_id, gen)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = FileVersionKey(ino_id: 5, gen: 3)
expect(key.gen).to_equal(3)
```

</details>

#### FILE_VERSION row round-trips

1. tbl insert
   - Expected: got.root_extent_ref equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.file_version()
val row = FileVersionRow(ino_id: 5, gen: 3, root_extent_ref: 0, version_flags: 0)
tbl.insert(row).unwrap()
val got = tbl.get(FileVersionKey(ino_id: 5, gen: 3)).unwrap()
expect(got.root_extent_ref).to_equal(0)
```

</details>

### DBFS Schema — EXTENT_REF table

#### EXTENT_REF key is (ino_id, gen, logical_offset)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = ExtentRefKey(ino_id: 1, gen: 0, logical_offset: 4096)
expect(key.logical_offset).to_equal(4096)
```

</details>

#### EXTENT_REF row round-trips

1. tbl insert
   - Expected: got.extent_id equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.extent_ref()
val row = ExtentRefRow(ino_id: 1, gen: 0, logical_offset: 0, length: 8192, extent_id: 7)
tbl.insert(row).unwrap()
val got = tbl.get(ExtentRefKey(ino_id: 1, gen: 0, logical_offset: 0)).unwrap()
expect(got.extent_id).to_equal(7)
```

</details>

### DBFS Schema — EXTENT and BLOCK_BLOB tables

#### EXTENT row round-trips

1. tbl insert
   - Expected: got.blob_id equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.extent()
val row = ExtentRow(extent_id: 7, blob_id: 3, offset_in_blob: 0,
                    length: 8192, checksum: 0, compression: 0,
                    birth_gen: 1, storage_class: 0)
tbl.insert(row).unwrap()
val got = tbl.get(ExtentKey(extent_id: 7)).unwrap()
expect(got.blob_id).to_equal(3)
```

</details>

#### BLOCK_BLOB row round-trips

1. tbl insert
   - Expected: got.length equals `65536`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.block_blob()
val row = BlockBlobRow(blob_id: 3, backend: 0, backend_addr: 0, length: 65536)
tbl.insert(row).unwrap()
val got = tbl.get(BlockBlobKey(blob_id: 3)).unwrap()
expect(got.length).to_equal(65536)
```

</details>

### DBFS Schema — XATTR, ACL_ENTRY, TXN, WAL_RECORD, STORAGE_CLASS

#### XATTR row round-trips

1. tbl insert
   - Expected: got.value equals `dbfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.xattr()
val row = XattrRow(ino_id: 1, name: "user.tag", value: "dbfs")
tbl.insert(row).unwrap()
val got = tbl.get(XattrKey(ino_id: 1, name: "user.tag")).unwrap()
expect(got.value).to_equal("dbfs")
```

</details>

#### TXN row round-trips

1. tbl insert
   - Expected: got.status equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.txn()
val row = TxnRow(txn_id: 1, status: 1, lsn_first: 10, lsn_last: 20)
tbl.insert(row).unwrap()
val got = tbl.get(TxnKey(txn_id: 1)).unwrap()
expect(got.status).to_equal(1)
```

</details>

#### STORAGE_CLASS has 6 static rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tbl = SchemaTable.storage_class()
val rows = tbl.scan_all().unwrap()
expect(rows.len()).to_equal(6)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
