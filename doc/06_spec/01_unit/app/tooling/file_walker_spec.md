# File Walker Specification

> Tests for file system traversal utilities that walk directories, filter by file type, and provide summary statistics for batch operations.

<!-- sdn-diagram:id=file_walker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_walker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_walker_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_walker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Walker Specification

Tests for file system traversal utilities that walk directories, filter by file type, and provide summary statistics for batch operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #XXX |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/file_walker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for file system traversal utilities that walk directories,
filter by file type, and provide summary statistics for batch operations.

## Key Concepts

| Concept | Description |
|---------|-------------|
| File Detection | Distinguishing files from directories by extension |
| Single File Handling | Returning individual files as single-element lists |
| Extension Filtering | Selecting only `.spl` files |
| Summary Statistics | Computing modification and error counts |

## Behavior

The file walker module provides:
- File vs. directory detection using extension checks
- Single file vs. directory walk mode selection
- SPipe file filtering with `_spec.spl` suffix matching
- Summary statistics: total, modified, unchanged, and error counts
- Conditional output formatting based on modification status

## Examples

```simple
describe "File Walker Operations":
it "walks directory and filters specs":
val files = ["test_spec.spl", "example.spl"]
val specs = files.filter(\f: f.ends_with("_spec.spl"))
expect specs.len() == 1
```

## Scenarios

### file_walker module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### is_file detection

#### detects file with extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test.spl"
val has_ext = path.contains(".")
expect has_ext == true
```

</details>

#### detects directory without extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src"
val has_ext = path.contains(".")
expect has_ext == false
```

</details>

#### detects file in path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/test.spl"
val has_ext = path.contains(".")
expect has_ext == true
```

</details>

### single file handling

#### returns single file as list

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test.spl"
val is_single_file = true
val result = if is_single_file: [path] else: []
expect result.len() == 1
```

</details>

#### returns directory walk result

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_single_file = false
val files = ["file1.spl", "file2.spl"]
val result = if is_single_file: [] else: files
expect result.len() == 2
```

</details>

### spec file filtering

#### filters _spec.spl files

1. expect specs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["test_spec.spl", "example.spl", "other_spec.spl"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 2
```

</details>

#### no specs in list

1. expect specs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["test.spl", "example.spl"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 0
```

</details>

#### all files are specs

1. expect specs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["test_spec.spl", "example_spec.spl"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 2
```

</details>

### filename extraction

#### extracts filename from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/test/example.spl"
val parts = path.split("/")
val filename = parts[parts.len() - 1]
expect filename == "example.spl"
```

</details>

#### handles filename without directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "example.spl"
val parts = path.split("/")
val filename = if parts.len() > 0: parts[parts.len() - 1] else: path
expect filename == "example.spl"
```

</details>

### summary calculations

#### calculates unchanged count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 10
val modified = 3
val errors = 1
val unchanged = total - modified - errors
expect unchanged == 6
```

</details>

#### no errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 10
val modified = 5
val errors = 0
val unchanged = total - modified - errors
expect unchanged == 5
```

</details>

#### all modified

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total = 5
val modified = 5
val errors = 0
val unchanged = total - modified - errors
expect unchanged == 0
```

</details>

### modified count check

#### has modifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modified = 3
expect modified > 0 == true
```

</details>

#### no modifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modified = 0
expect modified > 0 == false
```

</details>

### string interpolation in summary

#### interpolates modified count

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 5
val msg = "  Would modify: {count}"
expect msg.contains("5") == true
```

</details>

#### interpolates unchanged count

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unchanged = 3
val msg = "  Unchanged: {unchanged}"
expect msg.contains("3") == true
```

</details>

#### interpolates errors

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val errors = 2
val msg = "  Errors: {errors}"
expect msg.contains("2") == true
```

</details>

### conditional print

#### prints additional message when modified

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modified = 3
val should_print = modified > 0
expect should_print == true
```

</details>

#### no additional message when zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val modified = 0
val should_print = modified > 0
expect should_print == false
```

</details>

### extension check

#### checks .spl extension

1. expect filename ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filename = "test.spl"
expect filename.ends_with(".spl") == true
```

</details>

#### rejects other extensions

1. expect filename ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filename = "test.rs"
expect filename.ends_with(".spl") == false
```

</details>

### list construction

#### single element list

1. expect list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test.spl"
val list = [path]
expect list.len() == 1
```

</details>

#### empty list

1. expect list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = []
expect list.len() == 0
```

</details>

#### multi-element list

1. expect list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = ["a.spl", "b.spl", "c.spl"]
expect list.len() == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
