# Bulk Validate Path Handling Specification

> Tests for path normalization, dot-directory handling, file extension detection, and CMM file identification in the bulk validator. Covers the bug where rt_dir_list() callers could not handle paths containing `.`, `..`, or double slashes, and the heuristic that mistakenly treated directories as files (or vice versa).

<!-- sdn-diagram:id=bulk_validate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bulk_validate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bulk_validate_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bulk_validate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 80 | 80 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bulk Validate Path Handling Specification

Tests for path normalization, dot-directory handling, file extension detection, and CMM file identification in the bulk validator. Covers the bug where rt_dir_list() callers could not handle paths containing `.`, `..`, or double slashes, and the heuristic that mistakenly treated directories as files (or vice versa).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-BULK-PATH |
| Category | Tooling |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/usage/cmm_lsp/bulk_validate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for path normalization, dot-directory handling, file extension detection,
and CMM file identification in the bulk validator. Covers the bug where
rt_dir_list() callers could not handle paths containing `.`, `..`, or
double slashes, and the heuristic that mistakenly treated directories
as files (or vice versa).

## Key Concepts

| Concept | Description |
|---------|-------------|
| normalize_path | Resolves `.`, `..`, double slashes, trailing slashes |
| is_likely_directory | Heuristic: no extension = directory, dotfile = skip |
| is_cmm_file | Case-insensitive `.cmm` extension check |
| collect_cmm_files | Recursive directory traversal with dot-dir safety |

## Scenarios

### normalize_path

#### simple paths

#### returns identity for clean paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("/opt/t32/demo")).to_equal("/opt/t32/demo")
```

</details>

#### returns identity for relative clean paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo/bar/baz")).to_equal("foo/bar/baz")
```

</details>

#### returns identity for root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("/")).to_equal("/")
```

</details>

#### current directory dot

#### resolves single dot to current dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path(".")).to_equal(".")
```

</details>

#### resolves leading dot-slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("./foo")).to_equal("foo")
```

</details>

#### resolves middle dot component

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo/./bar")).to_equal("foo/bar")
```

</details>

#### resolves trailing dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo/bar/.")).to_equal("foo/bar")
```

</details>

#### resolves multiple consecutive dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("./foo/./bar/./baz")).to_equal("foo/bar/baz")
```

</details>

#### resolves dot after absolute path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("/opt/./t32/./demo")).to_equal("/opt/t32/demo")
```

</details>

#### parent directory double-dot

#### resolves trailing parent ref

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo/bar/..")).to_equal("foo")
```

</details>

#### resolves middle parent ref

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo/bar/../baz")).to_equal("foo/baz")
```

</details>

#### resolves multiple parent refs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("a/b/c/../../d")).to_equal("a/d")
```

</details>

#### resolves parent at root — stays at root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("/..")).to_equal("/")
```

</details>

#### resolves complex mixed dot and dotdot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("a/./b/../c/./d/../e")).to_equal("a/c/e")
```

</details>

#### handles going above relative root with dotdot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("../foo")).to_equal("../foo")
```

</details>

#### handles double dotdot above relative root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("../../foo/bar")).to_equal("../../foo/bar")
```

</details>

#### double slashes

#### collapses double slash in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo//bar")).to_equal("foo/bar")
```

</details>

#### collapses triple slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo///bar")).to_equal("foo/bar")
```

</details>

#### collapses double slash at start of absolute path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("//opt/t32")).to_equal("/opt/t32")
```

</details>

#### collapses double slash with dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path(".//foo/./bar//baz")).to_equal("foo/bar/baz")
```

</details>

#### trailing slashes

#### strips trailing slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo/bar/")).to_equal("foo/bar")
```

</details>

#### strips multiple trailing slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo/bar///")).to_equal("foo/bar")
```

</details>

#### strips trailing slash on absolute path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("/opt/t32/")).to_equal("/opt/t32")
```

</details>

#### empty and edge cases

#### returns dot for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("")).to_equal(".")
```

</details>

#### handles single component

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("foo")).to_equal("foo")
```

</details>

#### handles dot-dot only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("..")).to_equal("..")
```

</details>

#### handles deeply nested dotdot collapse

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("a/b/c/d/e/../../../../f")).to_equal("a/f")
```

</details>

#### bug reproduction — paths that caused rt_dir_list failures

#### reproduces: dot-slash prefix ./subdir

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("./demo/practice")).to_equal("demo/practice")
```

</details>

#### reproduces: middle dotdot dir/subdir/../other

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("/opt/t32/demo/../scripts")).to_equal("/opt/t32/scripts")
```

</details>

#### reproduces: double slash from string concat

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("/opt/t32//demo")).to_equal("/opt/t32/demo")
```

</details>

#### reproduces: complex mixed path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_path("./demo/./practice/../scripts//cmm/./")).to_equal("demo/scripts/cmm")
```

</details>

### is_cmm_file

#### positive matches

#### matches lowercase .cmm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.cmm")).to_equal(true)
```

</details>

#### matches uppercase .CMM

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.CMM")).to_equal(true)
```

</details>

#### matches mixed case .Cmm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.Cmm")).to_equal(true)
```

</details>

#### matches mixed case .cMM

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.cMM")).to_equal(true)
```

</details>

#### matches mixed case .CMm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.CMm")).to_equal(true)
```

</details>

#### matches long filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("my_long_script_name.cmm")).to_equal(true)
```

</details>

#### matches filename with dots

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("script.v2.cmm")).to_equal(true)
```

</details>

#### matches minimum length name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("a.cmm")).to_equal(true)
```

</details>

#### negative matches

#### rejects .txt extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.txt")).to_equal(false)
```

</details>

#### rejects .c extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.c")).to_equal(false)
```

</details>

#### rejects .cmm prefix without dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("cmm")).to_equal(false)
```

</details>

#### rejects too short name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file(".cmm")).to_equal(false)
```

</details>

#### rejects partial extension .cm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.cm")).to_equal(false)
```

</details>

#### rejects .cmmx extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("test.cmmx")).to_equal(false)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("")).to_equal(false)
```

</details>

#### rejects no extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cmm_file("testfile")).to_equal(false)
```

</details>

### is_likely_directory

#### entries that are likely directories

#### detects name without extension as directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("demo")).to_equal(true)
```

</details>

#### detects name without extension — underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("my_scripts")).to_equal(true)
```

</details>

#### detects name without extension — digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("t32")).to_equal(true)
```

</details>

#### detects name with very long pseudo-extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("file.longextname")).to_equal(true)
```

</details>

#### entries that are likely files

#### detects .cmm as file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("test.cmm")).to_equal(false)
```

</details>

#### detects .txt as file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("readme.txt")).to_equal(false)
```

</details>

#### detects .c as file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("main.c")).to_equal(false)
```

</details>

#### detects .h as file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("header.h")).to_equal(false)
```

</details>

#### detects .py as file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("script.py")).to_equal(false)
```

</details>

#### detects .cmm uppercase as file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("TEST.CMM")).to_equal(false)
```

</details>

#### hidden entries — should be skipped (returns false)

#### skips .git directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory(".git")).to_equal(false)
```

</details>

#### skips .svn directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory(".svn")).to_equal(false)
```

</details>

#### skips .gitignore file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory(".gitignore")).to_equal(false)
```

</details>

#### skips .hidden

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory(".hidden")).to_equal(false)
```

</details>

#### skips dotfile with extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory(".bashrc")).to_equal(false)
```

</details>

#### edge cases

#### handles single char name as directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_likely_directory("a")).to_equal(true)
```

</details>

#### handles name ending with dot only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "file." has ext_len = 0, so not 1..4 → treated as directory
expect(is_likely_directory("file.")).to_equal(true)
```

</details>

### contains

#### basic matches

#### finds needle at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("Unterminated block", "Unterminated")).to_equal(true)
```

</details>

#### finds needle in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("Line 5: Expected expression", "Expected")).to_equal(true)
```

</details>

#### finds needle at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("something unexpected", "unexpected")).to_equal(true)
```

</details>

#### finds exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("hello", "hello")).to_equal(true)
```

</details>

#### no matches

#### returns false for missing needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("hello world", "xyz")).to_equal(false)
```

</details>

#### returns false when needle longer than haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("hi", "hello world")).to_equal(false)
```

</details>

#### returns false for empty haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("", "x")).to_equal(false)
```

</details>

#### edge cases

#### finds empty needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("hello", "")).to_equal(true)
```

</details>

#### handles single char needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("abc", "b")).to_equal(true)
```

</details>

#### handles single char miss

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("abc", "z")).to_equal(false)
```

</details>

#### handles repeated pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains("aaabaaab", "aaab")).to_equal(true)
```

</details>

### starts_with

#### matches

#### matches prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with("trace32 encrypted", "trace32")).to_equal(true)
```

</details>

#### matches full string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with("hello", "hello")).to_equal(true)
```

</details>

#### matches empty prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with("anything", "")).to_equal(true)
```

</details>

#### no matches

#### rejects wrong prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with("hello", "world")).to_equal(false)
```

</details>

#### rejects longer prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(starts_with("hi", "hello")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 80 |
| Active scenarios | 80 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
