# Path Utils Specification

> Tests covering Path Utilities, Filename Extraction, Directory Name, Parent Directory, Path Joining, Extension, Stem, Has Extension, Path Normalization, Absolute Path, Make Relative, Split Path, Complex Scenarios.

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

- extracts filename from unix path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts filename from unix path")
expect get_filename("/home/user/file.txt") == "file.txt"
expect get_filename("/home/user/") == ""
expect get_filename("file.txt") == "file.txt"
```

</details>

#### extracts filename from windows path

- extracts filename from windows path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts filename from windows path")
expect get_filename("C:\\Users\\user\\file.txt") == "file.txt"
expect get_filename("C:\\Program Files\\app.exe") == "app.exe"
```

</details>

#### handles edge cases

- handles edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles edge cases")
expect get_filename("") == ""
expect get_filename("/") == ""
expect get_filename("simple_file") == "simple_file"
```

</details>

### Directory Name

#### gets directory name

- gets directory name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets directory name")
expect get_dir_name("/home/user/documents") == "documents"
expect get_dir_name("/home/user/documents/") == "documents"
```

</details>

### Parent Directory

#### gets parent dir unix

- gets parent dir unix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets parent dir unix")
expect get_parent_dir("/home/user/file.txt") == "/home/user"
expect get_parent_dir("/home/user/") == "/home"
expect get_parent_dir("/home") == "/"
```

</details>

#### returns option for parent

- returns option for parent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns option for parent")
val result = get_parent_dir_option("/home/user/file.txt")
expect result == "/home/user"
```

</details>

#### returns nil for no parent

- returns nil for no parent


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for no parent")
val result = get_parent_dir_option("file.txt")
expect result == nil
```

</details>

### Path Joining

#### joins unix paths

- joins unix paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins unix paths")
expect join_path("/home/user", "file.txt") == "/home/user/file.txt"
expect join_path("/home/user/", "file.txt") == "/home/user/file.txt"
```

</details>

#### handles edge cases

- handles edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles edge cases")
expect join_path("", "file.txt") == "file.txt"
expect join_path("/home", "") == "/home"
expect join_path("", "") == ""
```

</details>

### Extension

#### gets extension

- gets extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets extension")
expect get_extension("file.txt") == "txt"
expect get_extension("archive.tar.gz") == "gz"
expect get_extension("/path/to/file.json") == "json"
```

</details>

#### returns empty for no extension

- returns empty for no extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for no extension")
expect get_extension("README") == ""
expect get_extension("/path/to/file") == ""
expect get_extension("") == ""
```

</details>

#### handles hidden files

- handles hidden files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles hidden files")
expect get_extension(".gitignore") == ""
expect get_extension(".config.yml") == "yml"
```

</details>

### Stem

#### gets stem

- gets stem


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets stem")
expect get_stem("file.txt") == "file"
expect get_stem("archive.tar.gz") == "archive.tar"
expect get_stem("/path/to/document.pdf") == "document"
```

</details>

#### handles no extension

- handles no extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles no extension")
expect get_stem("README") == "README"
expect get_stem("Makefile") == "Makefile"
```

</details>

### Has Extension

#### checks extension

- checks extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks extension")
expect has_extension("file.txt", "txt")
expect has_extension("file.txt", ".txt")
expect has_extension("archive.TAR", "tar")
```

</details>

#### returns false for wrong extension

- returns false for wrong extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for wrong extension")
expect not has_extension("file.txt", "pdf")
expect not has_extension("README", "txt")
```

</details>

### Path Normalization

#### normalizes backslashes

- normalizes backslashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes backslashes")
expect normalize_path("C:\\Users\\user\\file.txt") == "C:/Users/user/file.txt"
expect normalize_path("/home/user/file.txt") == "/home/user/file.txt"
expect normalize_path("path\\to\\file") == "path/to/file"
```

</details>

### Absolute Path

#### detects unix absolute paths

- detects unix absolute paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects unix absolute paths")
expect is_absolute_path("/home/user/file.txt")
expect is_absolute_path("/")
expect not is_absolute_path("relative/path")
```

</details>

#### detects windows absolute paths

- detects windows absolute paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects windows absolute paths")
expect is_absolute_path("C:\\Users\\user\\file.txt")
expect is_absolute_path("D:/data/file.dat")
expect not is_absolute_path("relative\\path")
```

</details>

#### handles edge cases

- handles edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles edge cases")
expect not is_absolute_path("")
expect not is_absolute_path("file.txt")
```

</details>

### Make Relative

#### makes path relative

- makes path relative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes path relative")
expect make_relative("/home/user/docs/file.txt", "/home/user") == "docs/file.txt"
expect make_relative("/home/user/file.txt", "/home/user") == "file.txt"
```

</details>

#### returns original for no common prefix

- returns original for no common prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns original for no common prefix")
val result = make_relative("/var/log/file.txt", "/home/user")
expect result == "/var/log/file.txt"
```

</details>

### Split Path

#### splits unix path

- splits unix path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits unix path")
val parts = split_path("/home/user/documents/file.txt")
expect parts.len() == 4
expect parts[0] == "home"
expect parts[1] == "user"
expect parts[2] == "documents"
expect parts[3] == "file.txt"
```

</details>

#### splits relative path

- splits relative path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits relative path")
val parts = split_path("docs/file.txt")
expect parts.len() == 2
expect parts[0] == "docs"
expect parts[1] == "file.txt"
```

</details>

#### handles empty path

- handles empty path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty path")
val parts = split_path("")
expect parts.len() == 0
```

</details>

### Complex Scenarios

#### manipulates complex path

- manipulates complex path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("manipulates complex path")
val path = "/home/user/projects/simple/src/main.spl"
expect get_filename(path) == "main.spl"
expect get_extension(path) == "spl"
expect get_stem(path) == "main"
expect get_parent_dir(path) == "/home/user/projects/simple/src"
```

</details>

#### builds path from components

- builds path from components


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds path from components")
val base = "/home/user"
val subdir = "projects"
val filename = "main.spl"
val step1 = join_path(base, subdir)
val final_path = join_path(step1, filename)
expect final_path == "/home/user/projects/main.spl"
```

</details>

#### converts relative path

- converts relative path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts relative path")
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
| Source | `test/unit/app/tooling/path_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Path Utilities, Filename Extraction, Directory Name, Parent Directory, Path Joining, Extension, Stem, Has Extension, Path Normalization, Absolute Path, Make Relative, Split Path, Complex Scenarios.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94b58b1ea63ef6200162a851c7c337fee8ba1c9811578013e511d695936abeee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94b58b1ea63ef6200162a851c7c337fee8ba1c9811578013e511d695936abeee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94b58b1ea63ef6200162a851c7c337fee8ba1c9811578013e511d695936abeee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/path_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/path_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/path_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/path_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/path_utils_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts filename from unix path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/path_utils_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts filename from windows path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/path_utils_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
