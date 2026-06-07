# Wine Kernel32 File Metadata Specification

> <details>

<!-- sdn-diagram:id=wine_kernel32_file_metadata_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_file_metadata_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_file_metadata_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_file_metadata_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 File Metadata Specification

## Scenarios

### Wine KERNEL32 file metadata bridge

#### executes standalone GetFileAttributesW for files and directories

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_attrs = wine_kernel32_execute_file_attributes(["GetFileAttributesW"], _table_with_file(), "C:\\hello.txt")
expect(file_attrs.ok).to_equal(true)
expect(file_attrs.attributes).to_equal(0x80)
expect(file_attrs.operations).to_equal("GetFileAttributesW")

val dir_attrs = wine_kernel32_execute_file_attributes(["GetFileAttributesW"], _table_with_directory(), "C:\\TempDir")
expect(dir_attrs.ok).to_equal(true)
expect(dir_attrs.attributes).to_equal(0x10)
expect(dir_attrs.operations).to_equal("GetFileAttributesW")
```

</details>

#### executes a bounded attributes, open, size, information, seek, and close sequence

1.  table with file
   - Expected: result.ok is true
   - Expected: result.handle equals `0x40`
   - Expected: result.attributes equals `0x80`
   - Expected: result.size equals `10`
   - Expected: result.information equals `0x100000 + 10`
   - Expected: result.pointer equals `6`
   - Expected: result.operations equals `GetFileAttributesW CreateFileW GetFileSize GetFileInformationByHandle SetFile... (full value in folded executable source)`
   - Expected: wine_nt_file_read(result.table, result.handle, 1).state equals `invalid-handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    6
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x40)
expect(result.attributes).to_equal(0x80)
expect(result.size).to_equal(10)
expect(result.information).to_equal(0x100000 + 10)
expect(result.pointer).to_equal(6)
expect(result.operations).to_equal("GetFileAttributesW CreateFileW GetFileSize GetFileInformationByHandle SetFilePointer CloseHandle")
expect(wine_nt_file_read(result.table, result.handle, 1).state).to_equal("invalid-handle")
```

</details>

#### keeps file metadata dispatch ordered and bounded

1.  table with file
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-file-metadata-sequence-expected:GetFileAttributesW`
2.  table with file
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`
   - Expected: attributes_extra.ok is false
   - Expected: attributes_extra.error equals `kernel32-file-metadata-sequence-count-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_file_metadata(
    ["CreateFileW", "GetFileAttributesW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    6
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-file-metadata-sequence-expected:GetFileAttributesW")

val wrong_family = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "HeapAlloc", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    6
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")

val attributes_extra = wine_kernel32_execute_file_attributes(["GetFileAttributesW", "CloseHandle"], _table_with_file(), "C:\\hello.txt")
expect(attributes_extra.ok).to_equal(false)
expect(attributes_extra.error).to_equal("kernel32-file-metadata-sequence-count-mismatch")
```

</details>

#### propagates metadata and pointer failures

1.  table with file
   - Expected: missing.ok is false
   - Expected: missing.error equals `GetFileAttributesW:file-not-found`
   - Expected: missing_attributes.ok is false
   - Expected: missing_attributes.error equals `GetFileAttributesW:file-not-found`
2.  table with file
   - Expected: past_eof.ok is false
   - Expected: past_eof.error equals `SetFilePointer:file-pointer-past-eof`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\missing.txt",
    0
)
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("GetFileAttributesW:file-not-found")

val missing_attributes = wine_kernel32_execute_file_attributes(["GetFileAttributesW"], _table_with_file(), "C:\\missing.txt")
expect(missing_attributes.ok).to_equal(false)
expect(missing_attributes.error).to_equal("GetFileAttributesW:file-not-found")

val past_eof = wine_kernel32_execute_file_metadata(
    ["GetFileAttributesW", "CreateFileW", "GetFileSize", "GetFileInformationByHandle", "SetFilePointer", "CloseHandle"],
    _table_with_file(),
    "C:\\hello.txt",
    99
)
expect(past_eof.ok).to_equal(false)
expect(past_eof.error).to_equal("SetFilePointer:file-pointer-past-eof")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_file_metadata_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 file metadata bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
