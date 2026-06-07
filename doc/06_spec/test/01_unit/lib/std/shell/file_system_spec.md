# File System Specification

> <details>

<!-- sdn-diagram:id=file_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File System Specification

## Scenarios

### File System FFI Functions

#### file operations

#### should check if file exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test file should exist
val result = file.exist("simple/std_lib/test/unit/shell/file_system_spec.spl")
expect(result)
```

</details>

#### should return false for non-existent files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = file.exist("/nonexistent/test/file.txt")
expect(not result)
```

</details>

#### should write and read text file

1. file write text
2. file remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/simple_test_file.txt"
val test_content = "Hello from Simple test!"

# Write to file
file.write_text(test_path, test_content)

# Read back
val read_content = file.read_text(test_path)
expect(read_content == test_content)

# Clean up
file.remove(test_path)
```

</details>

#### should append text to file

1. file write text
2. file append text
3. file remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/simple_test_append.txt"

# Write initial content
file.write_text(test_path, "Line 1\n")

# Append more content
file.append_text(test_path, "Line 2\n")

# Read all
val content = file.read_text(test_path)
expect(content == "Line 1\nLine 2\n")

# Clean up
file.remove(test_path)
```

</details>

#### should copy file

1. file write text
2. file copy
3. file remove
4. file remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/simple_test_src.txt"
val dest_path = "/tmp/simple_test_dest.txt"

# Write source file
file.write_text(src_path, "Copy me!")

# Copy it
file.copy(src_path, dest_path)

# Verify destination exists and has same content
expect(file.exist(dest_path))
val dest_content = file.read_text(dest_path)
expect(dest_content == "Copy me!")

# Clean up
file.remove(src_path)
file.remove(dest_path)
```

</details>

#### should rename/move file

1. file write text
2. file rename
3. file remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_path = "/tmp/simple_test_rename_src.txt"
val new_path = "/tmp/simple_test_rename_dest.txt"

# Write source file
file.write_text(src_path, "Move me!")

# Rename it
file.rename(src_path, new_path)

# Verify old doesn't exist, new does
expect(not file.exist(src_path))
expect(file.exist(new_path))
val content = file.read_text(new_path)
expect(content == "Move me!")

# Clean up
file.remove(new_path)
```

</details>

#### directory operations

#### should create and remove directory

1. dir create
2. dir remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_test_dir"

# Create directory
dir.create(test_dir)

# Verify it exists
expect(dir.exist(test_dir))

# Remove it
dir.remove(test_dir)

# Verify it's gone
expect(not dir.exist(test_dir))
```

</details>

#### should create recursive directory

1. dir create recursive
2. dir remove recursive


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_test/nested/deep"

# Create nested directories
dir.create_recursive(test_dir)

# Verify it exists
expect(dir.exist(test_dir))

# Clean up (recursive remove)
dir.remove_recursive("/tmp/simple_test")
```

</details>

#### should list directory entries

1. dir create
2. file write text
3. file write text
4. file write text
5. file remove
6. file remove
7. file remove
8. dir remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_test_list"

# Create directory
dir.create(test_dir)

# Create some files
file.write_text("{test_dir}/file1.txt", "content1")
file.write_text("{test_dir}/file2.txt", "content2")
file.write_text("{test_dir}/file3.txt", "content3")

# List entries
val entries = dir.list(test_dir)

# Should have 3 entries
expect(entries.len() == 3)

# Clean up
file.remove("{test_dir}/file1.txt")
file.remove("{test_dir}/file2.txt")
file.remove("{test_dir}/file3.txt")
dir.remove(test_dir)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/shell/file_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- File System FFI Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
