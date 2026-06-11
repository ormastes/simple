# Wine Kernel32 File Management Specification

> <details>

<!-- sdn-diagram:id=wine_kernel32_file_management_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_file_management_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_file_management_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_file_management_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 File Management Specification

## Scenarios

### Wine KERNEL32 file-management bridge

#### executes a bounded DeleteFileW sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_file_delete(["DeleteFileW"], _table_with_file(), "C:\\temp.tmp")

expect(result.ok).to_equal(true)
expect(result.operations).to_equal("DeleteFileW")
expect(wine_nt_file_get_attributes_w(result.table, "C:\\temp.tmp").state).to_equal("file-not-found")
```

</details>

#### executes bounded CopyFileW and MoveFileW sequences

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/common/wine_kernel32_file_management_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
