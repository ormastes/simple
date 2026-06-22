# Path Utils Specification

> 1. expect get filename

<!-- sdn-diagram:id=path_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=path_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

path_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=path_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Path Utils Specification

## Scenarios

### Path Utilities

### Filename Extraction

#### extracts filename from unix path

1. expect get filename
2. expect get filename
3. expect get filename


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_filename("/home/user/file.txt") == "file.txt"
expect get_filename("/home/user/") == ""
expect get_filename("file.txt") == "file.txt"
```

</details>

#### extracts filename from windows path

1. expect get filename
2. expect get filename


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_filename("C:\\Users\\user\\file.txt") == "file.txt"
expect get_filename("C:\\Program Files\\app.exe") == "app.exe"
```

</details>

#### handles edge cases

1. expect get filename
2. expect get filename
3. expect get filename


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_filename("") == ""
expect get_filename("/") == ""
expect get_filename("simple_file") == "simple_file"
```

</details>

### Directory Name

#### gets directory name

1. expect get dir name
2. expect get dir name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_dir_name("/home/user/documents") == "documents"
expect get_dir_name("/home/user/documents/") == "documents"
```

</details>

### Parent Directory

#### gets parent dir unix

1. expect get parent dir
2. expect get parent dir
3. expect get parent dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_parent_dir("/home/user/file.txt") == "/home/user"
expect get_parent_dir("/home/user/") == "/home"
expect get_parent_dir("/home") == "/"
```

</details>

#### returns option for parent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_parent_dir_option("/home/user/file.txt")
expect result == "/home/user"
```

</details>

#### returns nil for no parent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_parent_dir_option("file.txt")
expect result == nil
```

</details>

### Path Joining

#### joins unix paths

1. expect join path
2. expect join path


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect join_path("/home/user", "file.txt") == "/home/user/file.txt"
expect join_path("/home/user/", "file.txt") == "/home/user/file.txt"
```

</details>

#### handles edge cases

1. expect join path
2. expect join path
3. expect join path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect join_path("", "file.txt") == "file.txt"
expect join_path("/home", "") == "/home"
expect join_path("", "") == ""
```

</details>

### Extension

#### gets extension

1. expect get extension
2. expect get extension
3. expect get extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_extension("file.txt") == "txt"
expect get_extension("archive.tar.gz") == "gz"
expect get_extension("/path/to/file.json") == "json"
```

</details>

#### returns empty for no extension

1. expect get extension
2. expect get extension
3. expect get extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_extension("README") == ""
expect get_extension("/path/to/file") == ""
expect get_extension("") == ""
```

</details>

#### handles hidden files

1. expect get extension
2. expect get extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_extension(".gitignore") == ""
expect get_extension(".config.yml") == "yml"
```

</details>

### Stem

#### gets stem

1. expect get stem
2. expect get stem
3. expect get stem


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_stem("file.txt") == "file"
expect get_stem("archive.tar.gz") == "archive.tar"
expect get_stem("/path/to/document.pdf") == "document"
```

</details>

#### handles no extension

1. expect get stem
2. expect get stem


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_stem("README") == "README"
expect get_stem("Makefile") == "Makefile"
```

</details>

### Has Extension

#### checks extension

1. expect has extension
2. expect has extension
3. expect has extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect has_extension("file.txt", "txt")
expect has_extension("file.txt", ".txt")
expect has_extension("archive.TAR", "tar")
```

</details>

#### returns false for wrong extension

1. expect not has extension
2. expect not has extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not has_extension("file.txt", "pdf")
expect not has_extension("README", "txt")
```

</details>

### Path Normalization

#### normalizes backslashes

1. expect normalize path
2. expect normalize path
3. expect normalize path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect normalize_path("C:\\Users\\user\\file.txt") == "C:/Users/user/file.txt"
expect normalize_path("/home/user/file.txt") == "/home/user/file.txt"
expect normalize_path("path\\to\\file") == "path/to/file"
```

</details>

### Absolute Path

#### detects unix absolute paths

1. expect is absolute path
2. expect is absolute path
3. expect not is absolute path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_absolute_path("/home/user/file.txt")
expect is_absolute_path("/")
expect not is_absolute_path("relative/path")
```

</details>

#### detects windows absolute paths

1. expect is absolute path
2. expect is absolute path
3. expect not is absolute path


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_absolute_path("C:\\Users\\user\\file.txt")
expect is_absolute_path("D:/data/file.dat")
expect not is_absolute_path("relative\\path")
```

</details>

#### handles edge cases

1. expect not is absolute path
2. expect not is absolute path


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not is_absolute_path("")
expect not is_absolute_path("file.txt")
```

</details>

### Make Relative

#### makes path relative

1. expect make relative
2. expect make relative


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect make_relative("/home/user/docs/file.txt", "/home/user") == "docs/file.txt"
expect make_relative("/home/user/file.txt", "/home/user") == "file.txt"
```

</details>

#### returns original for no common prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = make_relative("/var/log/file.txt", "/home/user")
expect result == "/var/log/file.txt"
```

</details>

### Split Path

#### splits unix path

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_path("/home/user/documents/file.txt")
expect parts.len() == 4
expect parts[0] == "home"
expect parts[1] == "user"
expect parts[2] == "documents"
expect parts[3] == "file.txt"
```

</details>

#### splits relative path

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_path("docs/file.txt")
expect parts.len() == 2
expect parts[0] == "docs"
expect parts[1] == "file.txt"
```

</details>

#### handles empty path

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = split_path("")
expect parts.len() == 0
```

</details>

### Complex Scenarios

#### manipulates complex path

1. expect get filename
2. expect get extension
3. expect get stem
4. expect get parent dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/home/user/projects/simple/src/main.spl"
expect get_filename(path) == "main.spl"
expect get_extension(path) == "spl"
expect get_stem(path) == "main"
expect get_parent_dir(path) == "/home/user/projects/simple/src"
```

</details>

#### builds path from components

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = "/home/user"
val subdir = "projects"
val filename = "main.spl"
val step1 = join_path(base, subdir)
val final_path = join_path(step1, filename)
expect final_path == "/home/user/projects/main.spl"
```

</details>

#### converts relative path

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val absolute = "/home/user/projects/simple/src/main.spl"
val base = "/home/user/projects"
val relative = make_relative(absolute, base)
expect relative == "simple/src/main.spl"
val parts = split_path(relative)
expect parts.len() == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/path_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Path Utilities
- Filename Extraction
- Directory Name
- Parent Directory
- Path Joining
- Extension
- Stem
- Has Extension
- Path Normalization
- Absolute Path
- Make Relative
- Split Path
- Complex Scenarios

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
