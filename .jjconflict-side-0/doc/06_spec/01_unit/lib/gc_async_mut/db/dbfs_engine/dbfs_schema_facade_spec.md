# Dbfs Schema Facade Specification

> Tests covering gc_async_mut DBFS schema facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Schema Facade Specification

## Scenarios

### gc_async_mut DBFS schema facade

#### re-exports schema tables and file metadata helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports schema tables and file metadata helpers
   - Expected: inodes.insert(root).is_ok() is true
   - Expected: inodes.insert(file).is_ok() is true
   - Expected: dentries.insert(DentryRow(parent_ino: 1, name: "hello.txt", child_ino: 2, gen: 1)).is_ok() is true
   - Expected: inodes.get(InodeKey(ino_id: 2)).unwrap().size equals `5`
   - Expected: dentries.get(DentryKey(parent_ino: 1, name: "hello.txt")).unwrap().child_ino equals `2`
   - Expected: meta.is_file is true
   - Expected: check_read(meta, 1000, 1000) is true
   - Expected: check_write(meta, 1000, 1000) is true
   - Expected: check_exec(meta, 1000, 1000) is false
   - Expected: resolved.is_ok() is true
   - Expected: resolved.unwrap().ino_id equals `2`
   - Expected: batch_stat(1, "/", dentries, inodes).len() equals `1`
   - Expected: PERM_READ != PERM_WRITE is true
   - Expected: PERM_EXEC < PERM_READ is true
   - Expected: S_IFMT & S_IFREG equals `S_IFREG`
   - Expected: hint.ino_id equals `2`
   - Expected: entry.meta.is_file is true
   - Expected: ATTR_SIZE equals `size`
   - Expected: ATTR_MTIME equals `mtime`
   - Expected: ATTR_CTIME equals `ctime`
   - Expected: ATTR_UID equals `uid`
   - Expected: ATTR_GID equals `gid`
   - Expected: ATTR_MODE equals `mode`
   - Expected: versions.insert(version).is_ok() is true
   - Expected: versions.get(FileVersionKey(ino_id: 2, gen: 1)).unwrap().root_extent_ref equals `99`
   - Expected: extent_refs.insert(extent_ref).is_ok() is true
   - Expected: extent_refs.get(ExtentRefKey(ino_id: 2, gen: 1, logical_offset: 0)).unwrap().extent_id equals `42`
   - Expected: extents.insert(extent).is_ok() is true
   - Expected: extents.get(ExtentKey(extent_id: 42)).unwrap().blob_id equals `7`
   - Expected: block_blobs.insert(block_blob).is_ok() is true
   - Expected: block_blobs.get(BlockBlobKey(blob_id: 7)).unwrap().backend_addr equals `128`
   - Expected: xattrs.insert(xattr).is_ok() is true
   - Expected: xattrs.get(XattrKey(ino_id: 2, name: "user.mime_type")).unwrap().value equals `text/plain`
   - Expected: acl_entries.insert(acl_entry).is_ok() is true
   - Expected: acl_entries.get(AclEntryKey(ino_id: 2, principal: "user:1000")).unwrap().perms equals `7`
   - Expected: txns.insert(txn).is_ok() is true
   - Expected: txns.get(TxnKey(txn_id: 11)).unwrap().lsn_last equals `120`
   - Expected: wal_records.insert(wal_record).is_ok() is true
   - Expected: wal_records.get(WalRecordKey(lsn: 121)).unwrap().payload equals `commit`
   - Expected: storage_classes.insert(storage_class).is_ok() is true
   - Expected: storage_classes.get(StorageClassKey(class_id: 6)).unwrap().hints equals `ARCHIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 83 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports schema tables and file metadata helpers")
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
expect(S_IFMT & S_IFREG).to_equal(S_IFREG)
val hint = HintEntry(path: "/hello.txt", ino_id: 2, gen: 1, cached_at: 0, access_count: 3)
expect(hint.ino_id).to_equal(2)
val entry = DirEntry(name: "hello.txt", meta: meta)
expect(entry.meta.is_file).to_equal(true)
expect(ATTR_SIZE).to_equal("size")
expect(ATTR_MTIME).to_equal("mtime")
expect(ATTR_CTIME).to_equal("ctime")
expect(ATTR_UID).to_equal("uid")
expect(ATTR_GID).to_equal("gid")
expect(ATTR_MODE).to_equal("mode")
var versions = FileVersionTable.new()
val version = FileVersionRow(ino_id: 2, gen: 1, root_extent_ref: 99, version_flags: 7)
expect(versions.insert(version).is_ok()).to_equal(true)
expect(versions.get(FileVersionKey(ino_id: 2, gen: 1)).unwrap().root_extent_ref).to_equal(99)
var extent_refs = ExtentRefTable.new()
val extent_ref = ExtentRefRow(ino_id: 2, gen: 1, logical_offset: 0, length: 4096, extent_id: 42)
expect(extent_refs.insert(extent_ref).is_ok()).to_equal(true)
expect(extent_refs.get(ExtentRefKey(ino_id: 2, gen: 1, logical_offset: 0)).unwrap().extent_id).to_equal(42)
var extents = ExtentTable.new()
val extent = ExtentRow(
    extent_id: 42, blob_id: 7, offset_in_blob: 0, length: 4096,
    checksum: 123, compression: 0, birth_gen: 1, storage_class: 0
)
expect(extents.insert(extent).is_ok()).to_equal(true)
expect(extents.get(ExtentKey(extent_id: 42)).unwrap().blob_id).to_equal(7)
var block_blobs = BlockBlobTable.new()
val block_blob = BlockBlobRow(blob_id: 7, backend: 1, backend_addr: 128, length: 4096)
expect(block_blobs.insert(block_blob).is_ok()).to_equal(true)
expect(block_blobs.get(BlockBlobKey(blob_id: 7)).unwrap().backend_addr).to_equal(128)
var xattrs = XattrTable.new()
val xattr = XattrRow(ino_id: 2, name: "user.mime_type", value: "text/plain")
expect(xattrs.insert(xattr).is_ok()).to_equal(true)
expect(xattrs.get(XattrKey(ino_id: 2, name: "user.mime_type")).unwrap().value).to_equal("text/plain")
var acl_entries = AclEntryTable.new()
val acl_entry = AclEntryRow(ino_id: 2, principal: "user:1000", perms: 7, allow_deny: 1)
expect(acl_entries.insert(acl_entry).is_ok()).to_equal(true)
expect(acl_entries.get(AclEntryKey(ino_id: 2, principal: "user:1000")).unwrap().perms).to_equal(7)
var txns = TxnTable.new()
val txn = TxnRow(txn_id: 11, status: 1, lsn_first: 100, lsn_last: 120)
expect(txns.insert(txn).is_ok()).to_equal(true)
expect(txns.get(TxnKey(txn_id: 11)).unwrap().lsn_last).to_equal(120)
var wal_records = WalRecordTable.new()
val wal_record = WalRecordRow(lsn: 121, txn_id: 11, record_type: 2, payload: "commit")
expect(wal_records.insert(wal_record).is_ok()).to_equal(true)
expect(wal_records.get(WalRecordKey(lsn: 121)).unwrap().payload).to_equal("commit")
var storage_classes = StorageClassTable.new()
val storage_class = StorageClassRow(class_id: 6, backend_kind: 6, hints: "ARCHIVE")
expect(storage_classes.insert(storage_class).is_ok()).to_equal(true)
expect(storage_classes.get(StorageClassKey(class_id: 6)).unwrap().hints).to_equal("ARCHIVE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut DBFS schema facade.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ea0ad87bd678da5c8cffb9bb8501a1419f85b8491c49f40c2e0ddb9cf75ad57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ea0ad87bd678da5c8cffb9bb8501a1419f85b8491c49f40c2e0ddb9cf75ad57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ea0ad87bd678da5c8cffb9bb8501a1419f85b8491c49f40c2e0ddb9cf75ad57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports schema tables and file metadata helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
