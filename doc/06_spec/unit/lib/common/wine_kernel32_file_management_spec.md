# Wine Kernel32 File Management Specification

> Tests covering Wine KERNEL32 file-management bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 File Management Specification

## Scenarios

### Wine KERNEL32 file-management bridge

#### executes a bounded DeleteFileW sequence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes a bounded DeleteFileW sequence
   - Expected: result.ok is true
   - Expected: result.operations equals `DeleteFileW`
   - Expected: wine_nt_file_get_attributes_w(result.table, "C:\\temp.tmp").state equals `file-not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes a bounded DeleteFileW sequence")
val result = wine_kernel32_execute_file_delete(["DeleteFileW"], _table_with_file(), "C:\\temp.tmp")

expect(result.ok).to_equal(true)
expect(result.operations).to_equal("DeleteFileW")
expect(wine_nt_file_get_attributes_w(result.table, "C:\\temp.tmp").state).to_equal("file-not-found")
```

</details>

#### executes bounded CopyFileW and MoveFileW sequences

- executes bounded CopyFileW and MoveFileW sequences
   - Expected: copied.ok is true
   - Expected: copied.operations equals `CopyFileW`
   - Expected: wine_nt_file_get_attributes_w(copied.table, "C:\\temp.tmp").ok is true
   - Expected: wine_nt_file_get_attributes_w(copied.table, "C:\\copy.tmp").ok is true
   - Expected: moved.ok is true
   - Expected: moved.operations equals `MoveFileW`
   - Expected: wine_nt_file_get_attributes_w(moved.table, "C:\\copy.tmp").state equals `file-not-found`
   - Expected: wine_nt_file_get_attributes_w(moved.table, "C:\\moved.tmp").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes bounded CopyFileW and MoveFileW sequences")
val copied = wine_kernel32_execute_file_copy(["CopyFileW"], _table_with_file(), "C:\\temp.tmp", "C:\\copy.tmp", true)
expect(copied.ok).to_equal(true)
expect(copied.operations).to_equal("CopyFileW")
expect(wine_nt_file_get_attributes_w(copied.table, "C:\\temp.tmp").ok).to_equal(true)
expect(wine_nt_file_get_attributes_w(copied.table, "C:\\copy.tmp").ok).to_equal(true)

val moved = wine_kernel32_execute_file_move(["MoveFileW"], copied.table, "C:\\copy.tmp", "C:\\moved.tmp")
expect(moved.ok).to_equal(true)
expect(moved.operations).to_equal("MoveFileW")
expect(wine_nt_file_get_attributes_w(moved.table, "C:\\copy.tmp").state).to_equal("file-not-found")
expect(wine_nt_file_get_attributes_w(moved.table, "C:\\moved.tmp").ok).to_equal(true)
```

</details>

#### executes bounded CreateDirectoryW and RemoveDirectoryW sequences

- executes bounded CreateDirectoryW and RemoveDirectoryW sequences
   - Expected: created.ok is true
   - Expected: created.operations equals `CreateDirectoryW`
   - Expected: created.table.directories.len() equals `1`
   - Expected: removed.ok is true
   - Expected: removed.operations equals `RemoveDirectoryW`
   - Expected: removed.table.directories.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes bounded CreateDirectoryW and RemoveDirectoryW sequences")
val created = wine_kernel32_execute_directory_create(["CreateDirectoryW"], _table_with_file(), "C:\\TempDir")
expect(created.ok).to_equal(true)
expect(created.operations).to_equal("CreateDirectoryW")
expect(created.table.directories.len()).to_equal(1)

val removed = wine_kernel32_execute_directory_remove(["RemoveDirectoryW"], created.table, "C:\\TempDir")
expect(removed.ok).to_equal(true)
expect(removed.operations).to_equal("RemoveDirectoryW")
expect(removed.table.directories.len()).to_equal(0)
```

</details>

#### keeps file-management dispatch ordered and bounded

- keeps file-management dispatch ordered and bounded
   - Expected: extra.ok is false
   - Expected: extra.error equals `bridge-wrong-category:CloseHandle`
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`
   - Expected: wrong_copy.ok is false
   - Expected: wrong_copy.error equals `kernel32-file-management-sequence-expected:CopyFileW`
   - Expected: wrong_move.ok is false
   - Expected: wrong_move.error equals `kernel32-file-management-sequence-expected:MoveFileW`
   - Expected: wrong_create_dir.ok is false
   - Expected: wrong_create_dir.error equals `kernel32-file-management-sequence-expected:CreateDirectoryW`
   - Expected: wrong_remove_dir.ok is false
   - Expected: wrong_remove_dir.error equals `kernel32-file-management-sequence-expected:RemoveDirectoryW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps file-management dispatch ordered and bounded")
val extra = wine_kernel32_execute_file_delete(["DeleteFileW", "CloseHandle"], _table_with_file(), "C:\\temp.tmp")
expect(extra.ok).to_equal(false)
expect(extra.error).to_equal("bridge-wrong-category:CloseHandle")

val wrong_family = wine_kernel32_execute_file_delete(["HeapAlloc"], _table_with_file(), "C:\\temp.tmp")
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")

val wrong_copy = wine_kernel32_execute_file_copy(["DeleteFileW"], _table_with_file(), "C:\\temp.tmp", "C:\\copy.tmp", true)
expect(wrong_copy.ok).to_equal(false)
expect(wrong_copy.error).to_equal("kernel32-file-management-sequence-expected:CopyFileW")

val wrong_move = wine_kernel32_execute_file_move(["CopyFileW"], _table_with_file(), "C:\\temp.tmp", "C:\\moved.tmp")
expect(wrong_move.ok).to_equal(false)
expect(wrong_move.error).to_equal("kernel32-file-management-sequence-expected:MoveFileW")

val wrong_create_dir = wine_kernel32_execute_directory_create(["RemoveDirectoryW"], _table_with_file(), "C:\\TempDir")
expect(wrong_create_dir.ok).to_equal(false)
expect(wrong_create_dir.error).to_equal("kernel32-file-management-sequence-expected:CreateDirectoryW")

val wrong_remove_dir = wine_kernel32_execute_directory_remove(["CreateDirectoryW"], _table_with_file(), "C:\\TempDir")
expect(wrong_remove_dir.ok).to_equal(false)
expect(wrong_remove_dir.error).to_equal("kernel32-file-management-sequence-expected:RemoveDirectoryW")
```

</details>

#### propagates readiness, missing-file, and sharing-violation errors

- propagates readiness, missing-file, and sharing-violation errors
   - Expected: not_ready.ok is false
   - Expected: not_ready.error equals `DeleteFileW:missing-api-fd-write`
   - Expected: missing.ok is false
   - Expected: missing.error equals `DeleteFileW:file-not-found`
   - Expected: sharing.ok is false
   - Expected: sharing.error equals `DeleteFileW:sharing-violation`
   - Expected: copy_exists.ok is false
   - Expected: copy_exists.error equals `CopyFileW:file-exists`
   - Expected: copy_to_dir.ok is false
   - Expected: copy_to_dir.error equals `CopyFileW:directory-exists`
   - Expected: move_missing.ok is false
   - Expected: move_missing.error equals `MoveFileW:file-not-found`
   - Expected: move_from_dir.ok is false
   - Expected: move_from_dir.error equals `MoveFileW:directory-move-unsupported`
   - Expected: duplicate_dir.ok is false
   - Expected: duplicate_dir.error equals `CreateDirectoryW:directory-exists`
   - Expected: non_empty_dir.ok is false
   - Expected: non_empty_dir.error equals `RemoveDirectoryW:directory-not-empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates readiness, missing-file, and sharing-violation errors")
val blocked = wine_nt_file_table_new("fd-open fd-read", _all_async_features())
val not_ready = wine_kernel32_execute_file_delete(["DeleteFileW"], blocked, "C:\\temp.tmp")
expect(not_ready.ok).to_equal(false)
expect(not_ready.error).to_equal("DeleteFileW:missing-api-fd-write")

val missing = wine_kernel32_execute_file_delete(["DeleteFileW"], _table_with_file(), "C:\\missing.tmp")
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("DeleteFileW:file-not-found")

val table = _table_with_file()
val opened = wine_nt_file_create_w(table, "C:\\temp.tmp")
val sharing = wine_kernel32_execute_file_delete(["DeleteFileW"], opened.table, "C:\\temp.tmp")
expect(sharing.ok).to_equal(false)
expect(sharing.error).to_equal("DeleteFileW:sharing-violation")

val copy_exists = wine_kernel32_execute_file_copy(["CopyFileW"], _table_with_file(), "C:\\temp.tmp", "C:\\temp.tmp", true)
expect(copy_exists.ok).to_equal(false)
expect(copy_exists.error).to_equal("CopyFileW:file-exists")

val copy_to_dir = wine_kernel32_execute_file_copy(["CopyFileW"], wine_nt_file_table_add_directory(_table_with_file(), "C:\\dir"), "C:\\temp.tmp", "C:\\dir", true)
expect(copy_to_dir.ok).to_equal(false)
expect(copy_to_dir.error).to_equal("CopyFileW:directory-exists")

val move_missing = wine_kernel32_execute_file_move(["MoveFileW"], _table_with_file(), "C:\\missing.tmp", "C:\\moved.tmp")
expect(move_missing.ok).to_equal(false)
expect(move_missing.error).to_equal("MoveFileW:file-not-found")

val move_from_dir = wine_kernel32_execute_file_move(["MoveFileW"], wine_nt_file_table_add_directory(_table_with_file(), "C:\\dir"), "C:\\dir", "C:\\moved.tmp")
expect(move_from_dir.ok).to_equal(false)
expect(move_from_dir.error).to_equal("MoveFileW:directory-move-unsupported")

val with_dir = wine_nt_file_table_add_directory(_table_with_file(), "C:\\TempDir")
val duplicate_dir = wine_kernel32_execute_directory_create(["CreateDirectoryW"], with_dir, "C:\\TempDir")
expect(duplicate_dir.ok).to_equal(false)
expect(duplicate_dir.error).to_equal("CreateDirectoryW:directory-exists")

val non_empty_dir = wine_kernel32_execute_directory_remove(["RemoveDirectoryW"], wine_nt_file_table_add_file(with_dir, "C:\\TempDir\\child.txt", "child"), "C:\\TempDir")
expect(non_empty_dir.ok).to_equal(false)
expect(non_empty_dir.error).to_equal("RemoveDirectoryW:directory-not-empty")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_kernel32_file_management_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine KERNEL32 file-management bridge.
- Wine KERNEL32 file-management bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `c029ec400ae368032ffc73a1f09edf2bb1f1c7389c12565cab47e26ac72abee9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c029ec400ae368032ffc73a1f09edf2bb1f1c7389c12565cab47e26ac72abee9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c029ec400ae368032ffc73a1f09edf2bb1f1c7389c12565cab47e26ac72abee9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_kernel32_file_management_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_kernel32_file_management_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_kernel32_file_management_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_kernel32_file_management_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_kernel32_file_management_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_kernel32_file_management_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes a bounded DeleteFileW sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_file_management_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes bounded CopyFileW and MoveFileW sequences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_kernel32_file_management_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes bounded CreateDirectoryW and RemoveDirectoryW sequences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
