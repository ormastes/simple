# Wine Nt File Io Specification

> <details>

<!-- sdn-diagram:id=wine_nt_file_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_file_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_file_io_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_file_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt File Io Specification

## Scenarios

### Wine NT file I/O bridge

#### lists the modeled CreateFileW, ReadFile, GetFileType, and metadata calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = wine_nt_file_io_required_calls()
expect(calls.len()).to_equal(13)
expect(calls[0]).to_equal("CreateFileW")
expect(calls[2]).to_equal("GetFileType")
expect(calls[4]).to_equal("GetFileAttributesW")
expect(calls[6]).to_equal("GetFileInformationByHandle")
expect(calls[7]).to_equal("SetFilePointer")
expect(calls[8]).to_equal("DeleteFileW")
expect(calls[9]).to_equal("CopyFileW")
expect(calls[10]).to_equal("MoveFileW")
expect(calls[11]).to_equal("CreateDirectoryW")
expect(calls[12]).to_equal("RemoveDirectoryW")
```

</details>

#### blocks file table readiness until POSIX and async prerequisites pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_new("fd-open fd-read", _all_async_features())
expect(table.ready).to_equal(false)
expect(table.state).to_equal("missing-api-fd-write")
```

</details>

#### opens a modeled file and reads requested bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\hello.txt", "hello wine")
val opened = wine_nt_file_create_w(table, "C:\\hello.txt")
expect(opened.ok).to_equal(true)
expect(opened.handle).to_equal(0x40)
val read = wine_nt_file_read(opened.table, opened.handle, 5)
expect(read.ok).to_equal(true)
expect(read.data).to_equal("hello")
expect(read.bytes_read).to_equal(5)
```

</details>

#### advances the read cursor across ReadFile calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\hello.txt", "hello wine")
val opened = wine_nt_file_create_w(table, "C:\\hello.txt")
val first = wine_nt_file_read(opened.table, opened.handle, 6)
val second = wine_nt_file_read(first.table, opened.handle, 4)
expect(first.data).to_equal("hello ")
expect(second.data).to_equal("wine")
```

</details>

#### writes modeled file bytes at the current handle cursor

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\hello.txt", "hello wine")
val opened = wine_nt_file_create_w(table, "C:\\hello.txt")
val moved = wine_nt_file_set_pointer(opened.table, opened.handle, 6)
val written = wine_nt_file_write(moved.table, opened.handle, "Simple")
val reset = wine_nt_file_set_pointer(written.table, opened.handle, 0)
val read = wine_nt_file_read(reset.table, opened.handle, 12)

expect(written.ok).to_equal(true)
expect(written.state).to_equal("written")
expect(written.bytes_read).to_equal(6)
expect(read.data).to_equal("hello Simple")
```

</details>

#### closes handles and rejects reads after CloseHandle

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\hello.txt", "hello")
val opened = wine_nt_file_create_w(table, "C:\\hello.txt")
val closed = wine_nt_file_close(opened.table, opened.handle)
expect(closed.ok).to_equal(true)
expect(closed.state).to_equal("closed")
expect(wine_nt_file_read(closed.table, opened.handle, 1).state).to_equal("invalid-handle")
```

</details>

#### rejects invalid paths, missing files, invalid handles, and invalid read sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_new(_all_adapter_apis(), _all_async_features())
expect(wine_nt_file_create_w(table, "").state).to_equal("invalid-path")
expect(wine_nt_file_create_w(table, "C:\\missing.txt").state).to_equal("file-not-found")
expect(wine_nt_file_read(table, 0x40, 1).state).to_equal("invalid-handle")
expect(wine_nt_file_write(table, 0x40, "x").state).to_equal("invalid-handle")
val with_file = wine_nt_file_table_add_file(table, "C:\\hello.txt", "hello")
val opened = wine_nt_file_create_w(with_file, "C:\\hello.txt")
expect(wine_nt_file_read(opened.table, opened.handle, -1).state).to_equal("invalid-read-size")
```

</details>

#### returns deterministic file type, attributes, information, file size, and pointer movement

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\hello.txt", "hello wine")
val attrs = wine_nt_file_get_attributes_w(table, "C:\\hello.txt")
val opened = wine_nt_file_create_w(table, "C:\\hello.txt")
val file_type = wine_nt_file_get_type(opened.table, opened.handle)
val size = wine_nt_file_get_size(opened.table, opened.handle)
val info = wine_nt_file_get_information_by_handle(opened.table, opened.handle)
val moved = wine_nt_file_set_pointer(size.table, opened.handle, 6)
val read = wine_nt_file_read(moved.table, opened.handle, 4)

expect(file_type.ok).to_equal(true)
expect(file_type.value).to_equal(1)
expect(attrs.ok).to_equal(true)
expect(attrs.value).to_equal(0x80)
expect(size.ok).to_equal(true)
expect(size.value).to_equal(10)
expect(info.ok).to_equal(true)
expect(info.value).to_equal(0x100000 + 10)
expect(moved.ok).to_equal(true)
expect(moved.value).to_equal(6)
expect(read.data).to_equal("wine")
```

</details>

#### rejects invalid metadata and pointer requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\hello.txt", "hello")
val opened = wine_nt_file_create_w(table, "C:\\hello.txt")
expect(wine_nt_file_get_attributes_w(table, "C:\\missing.txt").state).to_equal("file-not-found")
expect(wine_nt_file_get_type(table, 0x99).state).to_equal("invalid-handle")
expect(wine_nt_file_get_information_by_handle(table, 0x99).state).to_equal("invalid-handle")
expect(wine_nt_file_get_size(table, 0x99).state).to_equal("invalid-handle")
expect(wine_nt_file_set_pointer(opened.table, opened.handle, -1).state).to_equal("invalid-file-pointer")
expect(wine_nt_file_set_pointer(opened.table, opened.handle, 99).state).to_equal("file-pointer-past-eof")
```

</details>

#### deletes closed modeled files and blocks deletion while a handle is open

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\temp.tmp", "temp")
val opened = wine_nt_file_create_w(table, "C:\\temp.tmp")
val blocked = wine_nt_file_delete_w(opened.table, "C:\\temp.tmp")
expect(blocked.ok).to_equal(false)
expect(blocked.state).to_equal("sharing-violation")

val closed = wine_nt_file_close(opened.table, opened.handle)
val deleted = wine_nt_file_delete_w(closed.table, "C:\\temp.tmp")
expect(deleted.ok).to_equal(true)
expect(deleted.state).to_equal("deleted")
expect(wine_nt_file_get_attributes_w(deleted.table, "C:\\temp.tmp").state).to_equal("file-not-found")
expect(wine_nt_file_delete_w(deleted.table, "C:\\missing.tmp").state).to_equal("file-not-found")
```

</details>

#### copies files with existing-destination and open-destination guards

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\source.txt", "copy me")
val copied = wine_nt_file_copy_w(table, "C:\\source.txt", "C:\\dest.txt", true)
expect(copied.ok).to_equal(true)
expect(copied.state).to_equal("copied")
expect(copied.bytes_read).to_equal(7)
expect(wine_nt_file_get_attributes_w(copied.table, "C:\\source.txt").ok).to_equal(true)
expect(wine_nt_file_get_attributes_w(copied.table, "C:\\dest.txt").ok).to_equal(true)

val already_there = wine_nt_file_copy_w(copied.table, "C:\\source.txt", "C:\\dest.txt", true)
expect(already_there.state).to_equal("file-exists")
val overwrite = wine_nt_file_copy_w(copied.table, "C:\\source.txt", "C:\\dest.txt", false)
expect(overwrite.ok).to_equal(true)

val opened_dest = wine_nt_file_create_w(copied.table, "C:\\dest.txt")
val sharing = wine_nt_file_copy_w(opened_dest.table, "C:\\source.txt", "C:\\dest.txt", false)
val missing = wine_nt_file_copy_w(table, "C:\\missing.txt", "C:\\dest.txt", true)
expect(sharing.state).to_equal("sharing-violation")
expect(missing.state).to_equal("file-not-found")
val with_directory = wine_nt_file_table_add_directory(table, "C:\\dir")
expect(wine_nt_file_copy_w(with_directory, "C:\\dir", "C:\\copy.txt", true).state).to_equal("directory-not-file")
expect(wine_nt_file_copy_w(with_directory, "C:\\source.txt", "C:\\dir", true).state).to_equal("directory-exists")
```

</details>

#### moves files and removes the source path

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_add_file(wine_nt_file_table_new(_all_adapter_apis(), _all_async_features()), "C:\\source.txt", "move me")
val moved = wine_nt_file_move_w(table, "C:\\source.txt", "C:\\dest.txt")
expect(moved.ok).to_equal(true)
expect(moved.state).to_equal("moved")
expect(moved.bytes_read).to_equal(7)
expect(wine_nt_file_get_attributes_w(moved.table, "C:\\source.txt").state).to_equal("file-not-found")
expect(wine_nt_file_get_attributes_w(moved.table, "C:\\dest.txt").ok).to_equal(true)

val opened = wine_nt_file_create_w(table, "C:\\source.txt")
expect(wine_nt_file_move_w(opened.table, "C:\\source.txt", "C:\\dest.txt").state).to_equal("sharing-violation")
expect(wine_nt_file_move_w(table, "C:\\missing.txt", "C:\\dest.txt").state).to_equal("file-not-found")
val with_directory = wine_nt_file_table_add_directory(table, "C:\\dir")
expect(wine_nt_file_move_w(with_directory, "C:\\dir", "C:\\moved.txt").state).to_equal("directory-move-unsupported")
expect(wine_nt_file_move_w(with_directory, "C:\\source.txt", "C:\\dir").state).to_equal("directory-exists")
```

</details>

#### creates and removes empty directories

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_new(_all_adapter_apis(), _all_async_features())
val created = wine_nt_file_create_directory_w(table, "C:\\TempDir")
expect(created.ok).to_equal(true)
expect(created.state).to_equal("directory-created")
expect(wine_nt_file_get_attributes_w(created.table, "C:\\TempDir").value).to_equal(0x10)
expect(created.table.directories.len()).to_equal(1)

val removed = wine_nt_file_remove_directory_w(created.table, "C:\\TempDir")
expect(removed.ok).to_equal(true)
expect(removed.state).to_equal("directory-removed")
expect(removed.table.directories.len()).to_equal(0)
```

</details>

#### rejects duplicate, conflicting, missing, non-empty, and invalid directories

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_new(_all_adapter_apis(), _all_async_features())
val with_dir = wine_nt_file_table_add_directory(table, "C:\\TempDir")
val with_file = wine_nt_file_table_add_file(with_dir, "C:\\TempDir\\child.txt", "child")

expect(wine_nt_file_create_directory_w(with_dir, "C:\\TempDir").state).to_equal("directory-exists")
expect(wine_nt_file_create_directory_w(wine_nt_file_table_add_file(table, "C:\\file.txt", "file"), "C:\\file.txt").state).to_equal("file-exists")
expect(wine_nt_file_create_directory_w(table, "").state).to_equal("invalid-path")
expect(wine_nt_file_remove_directory_w(table, "C:\\MissingDir").state).to_equal("directory-not-found")
expect(wine_nt_file_remove_directory_w(with_file, "C:\\TempDir").state).to_equal("directory-not-empty")
expect(wine_nt_file_remove_directory_w(with_dir, "").state).to_equal("invalid-path")
```

</details>

#### enumerates deterministic direct directory children

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_file_table_new(_all_adapter_apis(), _all_async_features())
val with_dir = wine_nt_file_table_add_directory(wine_nt_file_table_add_directory(table, "C:\\TempDir"), "C:\\TempDir\\SubDir")
val with_file = wine_nt_file_table_add_file(wine_nt_file_table_add_file(with_dir, "C:\\TempDir\\child.txt", "child"), "C:\\TempDir\\SubDir\\nested.txt", "nested")
val listed = wine_nt_file_query_directory_w(with_file, "C:\\TempDir")

expect(listed.ok).to_equal(true)
expect(listed.state).to_equal("directory-enumerated")
expect(listed.data).to_equal("child.txt")
expect(listed.bytes_read).to_equal(2)
expect(wine_nt_file_query_directory_w(with_file, "C:\\missing").state).to_equal("directory-not-found")
expect(wine_nt_file_query_directory_w(with_file, "C:\\TempDir\\child.txt").state).to_equal("directory-not-directory")
expect(wine_nt_file_query_directory_w(with_file, "").state).to_equal("invalid-path")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_file_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NT file I/O bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
