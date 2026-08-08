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

- file write text
- file remove
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Write a file, then check it exists
val test_path = "/tmp/simple_test_exist_probe.txt"
file.write_text(test_path, "probe")
val result = file.exist(test_path)
file.remove(test_path)
assert_true(result)
```

</details>

#### should return false for non-existent files

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = file.exist("/nonexistent/test/file.txt")
assert_false(result)
```

</details>

#### should write and read text file

- file write text
- assert true
- file remove


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
assert_true(read_content == test_content)

# Clean up
file.remove(test_path)
```

</details>

#### should append text to file

- file write text
- file append text
- assert true
- file remove


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
assert_true(content == "Line 1\nLine 2\n")

# Clean up
file.remove(test_path)
```

</details>

#### should copy file

- file write text
- file copy
- assert true
- assert true
- file remove
- file remove


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
assert_true(file.exist(dest_path))
val dest_content = file.read_text(dest_path)
assert_true(dest_content == "Copy me!")

# Clean up
file.remove(src_path)
file.remove(dest_path)
```

</details>

#### should rename/move file

- file write text
- file rename
- assert false
- assert true
- assert true
- file remove


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
assert_false(file.exist(src_path))
assert_true(file.exist(new_path))
val content = file.read_text(new_path)
assert_true(content == "Move me!")

# Clean up
file.remove(new_path)
```

</details>

#### directory operations

#### should create and remove directory

- dir create
- assert true
- dir remove
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_test_dir"

# Create directory
dir.create(test_dir)

# Verify it exists
assert_true(dir.exist(test_dir))

# Remove it
dir.remove(test_dir)

# Verify it's gone
assert_false(dir.exist(test_dir))
```

</details>

#### should create recursive directory

- dir create recursive
- assert true
- dir remove recursive


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_test/nested/deep"

# Create nested directories
dir.create_recursive(test_dir)

# Verify it exists
assert_true(dir.exist(test_dir))

# Clean up (recursive remove)
dir.remove_recursive("/tmp/simple_test")
```

</details>

#### should list directory entries

- dir create
- file write text
- file write text
- file write text
- assert true
- file remove
- file remove
- file remove
- dir remove


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
assert_true(entries.len() == 3)

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
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/std/shell/file_system_spec.spl` |
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
