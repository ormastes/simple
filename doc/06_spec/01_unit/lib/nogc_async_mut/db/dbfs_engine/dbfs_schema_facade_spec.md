# Dbfs Schema Facade Specification

> Tests covering nogc_async_mut DBFS schema facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Schema Facade Specification

## Scenarios

### nogc_async_mut DBFS schema facade

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


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
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
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut DBFS schema facade.
- nogc_async_mut DBFS schema facade

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

- Canonical SPipe generation for source `a08f19c9df21cb715a1af172bd55ac8c11bf4abc01f27be80884bec6ab2cf570`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a08f19c9df21cb715a1af172bd55ac8c11bf4abc01f27be80884bec6ab2cf570`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a08f19c9df21cb715a1af172bd55ac8c11bf4abc01f27be80884bec6ab2cf570`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports schema tables and file metadata helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
