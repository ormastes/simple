# Wine Kernel32 File Io Specification

> <details>

<!-- sdn-diagram:id=wine_kernel32_file_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_file_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_file_io_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_file_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 File Io Specification

## Scenarios

### Wine KERNEL32 file I/O bridge

#### executes a bounded CreateFileW, ReadFile, GetFileType, and CloseHandle sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", 5)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x40)
expect(result.data).to_equal("hello")
expect(result.bytes_read).to_equal(5)
expect(result.file_type).to_equal(1)
expect(result.operations).to_equal("CreateFileW ReadFile GetFileType CloseHandle")
expect(wine_nt_file_read(result.table, result.handle, 1).state).to_equal("invalid-handle")
```

</details>

#### keeps file I/O dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_file_io(["ReadFile", "CreateFileW", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", 5)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-file-io-sequence-expected:CreateFileW")

val wrong_family = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "HeapFree"], _table_with_file(), "C:\\hello.txt", 5)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapFree")

val missing_file = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\missing.txt", 5)
expect(missing_file.ok).to_equal(false)
expect(missing_file.error).to_equal("CreateFileW:file-not-found")
```

</details>

#### propagates NT file-table readiness and read errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked = wine_nt_file_table_new("fd-open fd-read", _all_async_features())
val not_ready = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], blocked, "C:\\hello.txt", 5)
expect(not_ready.ok).to_equal(false)
expect(not_ready.error).to_equal("CreateFileW:missing-api-fd-write")

val invalid_read = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", -1)
expect(invalid_read.ok).to_equal(false)
expect(invalid_read.error).to_equal("ReadFile:invalid-read-size")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_file_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 file I/O bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
