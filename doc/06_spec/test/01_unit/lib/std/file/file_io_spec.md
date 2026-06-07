# File Io Specification

> <details>

<!-- sdn-diagram:id=file_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_io_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Io Specification

## Scenarios

### File I/O FFI Functions

#### file existence checking

#### should check if file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with a file that should exist
val exists = file.is_file("simple/std_lib/test/unit/file/file_io_spec.spl")
expect(exists)
```

</details>

#### should return false for non-existent files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file.is_file("/nonexistent/file/path/test.txt")
expect(not exists)
```

</details>

#### file size retrieval

#### should get size of existing file

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test file should have non-zero size
match file.size("simple/std_lib/test/unit/file/file_io_spec.spl"):
    case Ok(size):
        expect(size > 0)
    case Err(e):
        fail("Expected Ok, got Err: {e}")
```

</details>

#### should return error for non-existent file

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match file.size("/nonexistent/file.txt"):
    case Ok(_):
        fail("Expected Err for non-existent file")
    case Err(_):
        pass  # Expected error
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/file/file_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- File I/O FFI Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
