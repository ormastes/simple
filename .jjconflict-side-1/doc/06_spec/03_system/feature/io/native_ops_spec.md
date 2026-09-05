# Native File and Directory Operations

> Tests native file and directory operations including file read/write, directory creation/listing, and path manipulation. Verifies that I/O operations correctly interact with the filesystem across supported platforms.

<!-- sdn-diagram:id=native_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_ops_spec -> std
native_ops_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native File and Directory Operations

Tests native file and directory operations including file read/write, directory creation/listing, and path manipulation. Verifies that I/O operations correctly interact with the filesystem across supported platforms.

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | In Progress |
| Source | `test/03_system/feature/io/native_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests native file and directory operations including file read/write, directory
creation/listing, and path manipulation. Verifies that I/O operations correctly
interact with the filesystem across supported platforms.

## Scenarios

### Native File Operations

#### creates and reads files

1. check
2. check
   - Expected: read_content equals `content`
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/simple_native_file_test.txt"
val content = "Hello from native SFFI!"

check(file_write(test_file, content))
check(file_exists(test_file))

val read_content = file_read(test_file)
expect(read_content).to_equal(content)

check(file_delete(test_file))
check(not file_exists(test_file))
```

</details>

#### copies files

1. file write
2. check
   - Expected: dst_content equals `Copy test`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "/tmp/simple_copy_src.txt"
val dst = "/tmp/simple_copy_dst.txt"

file_write(src, "Copy test")
check(file_copy(src, dst))

val dst_content = file_read(dst)
expect(dst_content).to_equal("Copy test")

file_delete(src)
file_delete(dst)
```

</details>

#### gets file size

1. file write
   - Expected: size equals `5`
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/simple_size_test.txt"
val content = "12345"

file_write(test_file, content)
val size = file_size_raw(test_file)
expect(size).to_equal(5)

file_delete(test_file)
```

</details>

### Native Directory Operations

#### creates directories

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_native_dir_test"

check(dir_create(test_dir, false))
check(is_dir(test_dir))
check(dir_remove_all(test_dir) == 0)
```

</details>

#### creates nested directories recursively

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_native_deep/sub1/sub2"

check(dir_create(test_dir, true))
check(is_dir(test_dir))
check(dir_remove_all("/tmp/simple_native_deep") == 0)
```

</details>

#### creates directory tree with dir_create_all

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_dir = "/tmp/simple_create_all/a/b/c"

check(dir_create_all(test_dir))
check(is_dir(test_dir))
check(dir_remove_all("/tmp/simple_create_all") == 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
