# Bulk Validate Path Handling Specification

> Tests for path normalization, dot-directory handling, file extension detection, and CMM file identification in the bulk validator. Covers the bug where rt_dir_list() callers could not handle paths containing `.`, `..`, or double slashes, and the heuristic that mistakenly treated directories as files (or vice versa).

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
| Source | `test/feature/usage/cmm_lsp/bulk_validate_spec.spl` |
| Updated | 2026-08-26 |
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

- returns identity for clean paths
   - Expected: normalize_path("/opt/t32/demo") equals `/opt/t32/demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns identity for clean paths")
expect(normalize_path("/opt/t32/demo")).to_equal("/opt/t32/demo")
```

</details>

#### returns identity for relative clean paths

- returns identity for relative clean paths
   - Expected: normalize_path("foo/bar/baz") equals `foo/bar/baz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns identity for relative clean paths")
expect(normalize_path("foo/bar/baz")).to_equal("foo/bar/baz")
```

</details>

#### returns identity for root

- returns identity for root
   - Expected: normalize_path("/") equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns identity for root")
expect(normalize_path("/")).to_equal("/")
```

</details>

#### current directory dot

#### resolves single dot to current dir

- resolves single dot to current dir
   - Expected: normalize_path(".") equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves single dot to current dir")
expect(normalize_path(".")).to_equal(".")
```

</details>

#### resolves leading dot-slash

- resolves leading dot-slash
   - Expected: normalize_path("./foo") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves leading dot-slash")
expect(normalize_path("./foo")).to_equal("foo")
```

</details>

#### resolves middle dot component

- resolves middle dot component
   - Expected: normalize_path("foo/./bar") equals `foo/bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves middle dot component")
expect(normalize_path("foo/./bar")).to_equal("foo/bar")
```

</details>

#### resolves trailing dot

- resolves trailing dot
   - Expected: normalize_path("foo/bar/.") equals `foo/bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves trailing dot")
expect(normalize_path("foo/bar/.")).to_equal("foo/bar")
```

</details>

#### resolves multiple consecutive dots

- resolves multiple consecutive dots
   - Expected: normalize_path("./foo/./bar/./baz") equals `foo/bar/baz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves multiple consecutive dots")
expect(normalize_path("./foo/./bar/./baz")).to_equal("foo/bar/baz")
```

</details>

#### resolves dot after absolute path

- resolves dot after absolute path
   - Expected: normalize_path("/opt/./t32/./demo") equals `/opt/t32/demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves dot after absolute path")
expect(normalize_path("/opt/./t32/./demo")).to_equal("/opt/t32/demo")
```

</details>

#### parent directory double-dot

#### resolves trailing parent ref

- resolves trailing parent ref
   - Expected: normalize_path("foo/bar/..") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves trailing parent ref")
expect(normalize_path("foo/bar/..")).to_equal("foo")
```

</details>

#### resolves middle parent ref

- resolves middle parent ref
   - Expected: normalize_path("foo/bar/../baz") equals `foo/baz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves middle parent ref")
expect(normalize_path("foo/bar/../baz")).to_equal("foo/baz")
```

</details>

#### resolves multiple parent refs

- resolves multiple parent refs
   - Expected: normalize_path("a/b/c/../../d") equals `a/d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves multiple parent refs")
expect(normalize_path("a/b/c/../../d")).to_equal("a/d")
```

</details>

#### resolves parent at root — stays at root

- resolves parent at root — stays at root
   - Expected: normalize_path("/..") equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves parent at root — stays at root")
expect(normalize_path("/..")).to_equal("/")
```

</details>

#### resolves complex mixed dot and dotdot

- resolves complex mixed dot and dotdot
   - Expected: normalize_path("a/./b/../c/./d/../e") equals `a/c/e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves complex mixed dot and dotdot")
expect(normalize_path("a/./b/../c/./d/../e")).to_equal("a/c/e")
```

</details>

#### handles going above relative root with dotdot

- handles going above relative root with dotdot
   - Expected: normalize_path("../foo") equals `../foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles going above relative root with dotdot")
expect(normalize_path("../foo")).to_equal("../foo")
```

</details>

#### handles double dotdot above relative root

- handles double dotdot above relative root
   - Expected: normalize_path("../../foo/bar") equals `../../foo/bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles double dotdot above relative root")
expect(normalize_path("../../foo/bar")).to_equal("../../foo/bar")
```

</details>

#### double slashes

#### collapses double slash in middle

- collapses double slash in middle
   - Expected: normalize_path("foo//bar") equals `foo/bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("collapses double slash in middle")
expect(normalize_path("foo//bar")).to_equal("foo/bar")
```

</details>

#### collapses triple slash

- collapses triple slash
   - Expected: normalize_path("foo///bar") equals `foo/bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("collapses triple slash")
expect(normalize_path("foo///bar")).to_equal("foo/bar")
```

</details>

#### collapses double slash at start of absolute path

- collapses double slash at start of absolute path
   - Expected: normalize_path("//opt/t32") equals `/opt/t32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("collapses double slash at start of absolute path")
expect(normalize_path("//opt/t32")).to_equal("/opt/t32")
```

</details>

#### collapses double slash with dots

- collapses double slash with dots
   - Expected: normalize_path(".//foo/./bar//baz") equals `foo/bar/baz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("collapses double slash with dots")
expect(normalize_path(".//foo/./bar//baz")).to_equal("foo/bar/baz")
```

</details>

#### trailing slashes

#### strips trailing slash

- strips trailing slash
   - Expected: normalize_path("foo/bar/") equals `foo/bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("strips trailing slash")
expect(normalize_path("foo/bar/")).to_equal("foo/bar")
```

</details>

#### strips multiple trailing slashes

- strips multiple trailing slashes
   - Expected: normalize_path("foo/bar///") equals `foo/bar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("strips multiple trailing slashes")
expect(normalize_path("foo/bar///")).to_equal("foo/bar")
```

</details>

#### strips trailing slash on absolute path

- strips trailing slash on absolute path
   - Expected: normalize_path("/opt/t32/") equals `/opt/t32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("strips trailing slash on absolute path")
expect(normalize_path("/opt/t32/")).to_equal("/opt/t32")
```

</details>

#### empty and edge cases

#### returns dot for empty string

- returns dot for empty string
   - Expected: normalize_path("") equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns dot for empty string")
expect(normalize_path("")).to_equal(".")
```

</details>

#### handles single component

- handles single component
   - Expected: normalize_path("foo") equals `foo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles single component")
expect(normalize_path("foo")).to_equal("foo")
```

</details>

#### handles dot-dot only

- handles dot-dot only
   - Expected: normalize_path("..") equals `..`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles dot-dot only")
expect(normalize_path("..")).to_equal("..")
```

</details>

#### handles deeply nested dotdot collapse

- handles deeply nested dotdot collapse
   - Expected: normalize_path("a/b/c/d/e/../../../../f") equals `a/f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles deeply nested dotdot collapse")
expect(normalize_path("a/b/c/d/e/../../../../f")).to_equal("a/f")
```

</details>

#### bug reproduction — paths that caused rt_dir_list failures

#### reproduces: dot-slash prefix ./subdir

- reproduces: dot-slash prefix ./subdir
   - Expected: normalize_path("./demo/practice") equals `demo/practice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reproduces: dot-slash prefix ./subdir")
expect(normalize_path("./demo/practice")).to_equal("demo/practice")
```

</details>

#### reproduces: middle dotdot dir/subdir/../other

- reproduces: middle dotdot dir/subdir/../other
   - Expected: normalize_path("/opt/t32/demo/../scripts") equals `/opt/t32/scripts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reproduces: middle dotdot dir/subdir/../other")
expect(normalize_path("/opt/t32/demo/../scripts")).to_equal("/opt/t32/scripts")
```

</details>

#### reproduces: double slash from string concat

- reproduces: double slash from string concat
   - Expected: normalize_path("/opt/t32//demo") equals `/opt/t32/demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reproduces: double slash from string concat")
expect(normalize_path("/opt/t32//demo")).to_equal("/opt/t32/demo")
```

</details>

#### reproduces: complex mixed path

- reproduces: complex mixed path
   - Expected: normalize_path("./demo/./practice/../scripts//cmm/./") equals `demo/scripts/cmm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reproduces: complex mixed path")
expect(normalize_path("./demo/./practice/../scripts//cmm/./")).to_equal("demo/scripts/cmm")
```

</details>

### is_cmm_file

#### positive matches

#### matches lowercase .cmm

- matches lowercase .cmm
   - Expected: is_cmm_file("test.cmm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches lowercase .cmm")
expect(is_cmm_file("test.cmm")).to_equal(true)
```

</details>

#### matches uppercase .CMM

- matches uppercase .CMM
   - Expected: is_cmm_file("test.CMM") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches uppercase .CMM")
expect(is_cmm_file("test.CMM")).to_equal(true)
```

</details>

#### matches mixed case .Cmm

- matches mixed case .Cmm
   - Expected: is_cmm_file("test.Cmm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches mixed case .Cmm")
expect(is_cmm_file("test.Cmm")).to_equal(true)
```

</details>

#### matches mixed case .cMM

- matches mixed case .cMM
   - Expected: is_cmm_file("test.cMM") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches mixed case .cMM")
expect(is_cmm_file("test.cMM")).to_equal(true)
```

</details>

#### matches mixed case .CMm

- matches mixed case .CMm
   - Expected: is_cmm_file("test.CMm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches mixed case .CMm")
expect(is_cmm_file("test.CMm")).to_equal(true)
```

</details>

#### matches long filename

- matches long filename
   - Expected: is_cmm_file("my_long_script_name.cmm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches long filename")
expect(is_cmm_file("my_long_script_name.cmm")).to_equal(true)
```

</details>

#### matches filename with dots

- matches filename with dots
   - Expected: is_cmm_file("script.v2.cmm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches filename with dots")
expect(is_cmm_file("script.v2.cmm")).to_equal(true)
```

</details>

#### matches minimum length name

- matches minimum length name
   - Expected: is_cmm_file("a.cmm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches minimum length name")
expect(is_cmm_file("a.cmm")).to_equal(true)
```

</details>

#### negative matches

#### rejects .txt extension

- rejects .txt extension
   - Expected: is_cmm_file("test.txt") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects .txt extension")
expect(is_cmm_file("test.txt")).to_equal(false)
```

</details>

#### rejects .c extension

- rejects .c extension
   - Expected: is_cmm_file("test.c") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects .c extension")
expect(is_cmm_file("test.c")).to_equal(false)
```

</details>

#### rejects .cmm prefix without dot

- rejects .cmm prefix without dot
   - Expected: is_cmm_file("cmm") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects .cmm prefix without dot")
expect(is_cmm_file("cmm")).to_equal(false)
```

</details>

#### rejects too short name

- rejects too short name
   - Expected: is_cmm_file(".cmm") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects too short name")
expect(is_cmm_file(".cmm")).to_equal(false)
```

</details>

#### rejects partial extension .cm

- rejects partial extension .cm
   - Expected: is_cmm_file("test.cm") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects partial extension .cm")
expect(is_cmm_file("test.cm")).to_equal(false)
```

</details>

#### rejects .cmmx extension

- rejects .cmmx extension
   - Expected: is_cmm_file("test.cmmx") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects .cmmx extension")
expect(is_cmm_file("test.cmmx")).to_equal(false)
```

</details>

#### rejects empty string

- rejects empty string
   - Expected: is_cmm_file("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects empty string")
expect(is_cmm_file("")).to_equal(false)
```

</details>

#### rejects no extension

- rejects no extension
   - Expected: is_cmm_file("testfile") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects no extension")
expect(is_cmm_file("testfile")).to_equal(false)
```

</details>

### is_likely_directory

#### entries that are likely directories

#### detects name without extension as directory

- detects name without extension as directory
   - Expected: is_likely_directory("demo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects name without extension as directory")
expect(is_likely_directory("demo")).to_equal(true)
```

</details>

#### detects name without extension — underscore

- detects name without extension — underscore
   - Expected: is_likely_directory("my_scripts") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects name without extension — underscore")
expect(is_likely_directory("my_scripts")).to_equal(true)
```

</details>

#### detects name without extension — digits

- detects name without extension — digits
   - Expected: is_likely_directory("t32") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects name without extension — digits")
expect(is_likely_directory("t32")).to_equal(true)
```

</details>

#### detects name with very long pseudo-extension

- detects name with very long pseudo-extension
   - Expected: is_likely_directory("file.longextname") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects name with very long pseudo-extension")
expect(is_likely_directory("file.longextname")).to_equal(true)
```

</details>

#### entries that are likely files

#### detects .cmm as file

- detects .cmm as file
   - Expected: is_likely_directory("test.cmm") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects .cmm as file")
expect(is_likely_directory("test.cmm")).to_equal(false)
```

</details>

#### detects .txt as file

- detects .txt as file
   - Expected: is_likely_directory("readme.txt") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects .txt as file")
expect(is_likely_directory("readme.txt")).to_equal(false)
```

</details>

#### detects .c as file

- detects .c as file
   - Expected: is_likely_directory("main.c") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects .c as file")
expect(is_likely_directory("main.c")).to_equal(false)
```

</details>

#### detects .h as file

- detects .h as file
   - Expected: is_likely_directory("header.h") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects .h as file")
expect(is_likely_directory("header.h")).to_equal(false)
```

</details>

#### detects .py as file

- detects .py as file
   - Expected: is_likely_directory("script.py") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects .py as file")
expect(is_likely_directory("script.py")).to_equal(false)
```

</details>

#### detects .cmm uppercase as file

- detects .cmm uppercase as file
   - Expected: is_likely_directory("TEST.CMM") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects .cmm uppercase as file")
expect(is_likely_directory("TEST.CMM")).to_equal(false)
```

</details>

#### hidden entries — should be skipped (returns false)

#### skips .git directory

- skips .git directory
   - Expected: is_likely_directory(".git") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips .git directory")
expect(is_likely_directory(".git")).to_equal(false)
```

</details>

#### skips .svn directory

- skips .svn directory
   - Expected: is_likely_directory(".svn") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips .svn directory")
expect(is_likely_directory(".svn")).to_equal(false)
```

</details>

#### skips .gitignore file

- skips .gitignore file
   - Expected: is_likely_directory(".gitignore") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips .gitignore file")
expect(is_likely_directory(".gitignore")).to_equal(false)
```

</details>

#### skips .hidden

- skips .hidden
   - Expected: is_likely_directory(".hidden") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips .hidden")
expect(is_likely_directory(".hidden")).to_equal(false)
```

</details>

#### skips dotfile with extension

- skips dotfile with extension
   - Expected: is_likely_directory(".bashrc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips dotfile with extension")
expect(is_likely_directory(".bashrc")).to_equal(false)
```

</details>

#### edge cases

#### handles single char name as directory

- handles single char name as directory
   - Expected: is_likely_directory("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles single char name as directory")
expect(is_likely_directory("a")).to_equal(true)
```

</details>

#### handles name ending with dot only

- handles name ending with dot only
   - Expected: is_likely_directory("file.") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles name ending with dot only")
# "file." has ext_len = 0, so not 1..4 → treated as directory
expect(is_likely_directory("file.")).to_equal(true)
```

</details>

### contains

#### basic matches

#### finds needle at start

- finds needle at start
   - Expected: contains("Unterminated block", "Unterminated") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds needle at start")
expect(contains("Unterminated block", "Unterminated")).to_equal(true)
```

</details>

#### finds needle in middle

- finds needle in middle
   - Expected: contains("Line 5: Expected expression", "Expected") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds needle in middle")
expect(contains("Line 5: Expected expression", "Expected")).to_equal(true)
```

</details>

#### finds needle at end

- finds needle at end
   - Expected: contains("something unexpected", "unexpected") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds needle at end")
expect(contains("something unexpected", "unexpected")).to_equal(true)
```

</details>

#### finds exact match

- finds exact match
   - Expected: contains("hello", "hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds exact match")
expect(contains("hello", "hello")).to_equal(true)
```

</details>

#### no matches

#### returns false for missing needle

- returns false for missing needle
   - Expected: contains("hello world", "xyz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns false for missing needle")
expect(contains("hello world", "xyz")).to_equal(false)
```

</details>

#### returns false when needle longer than haystack

- returns false when needle longer than haystack
   - Expected: contains("hi", "hello world") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns false when needle longer than haystack")
expect(contains("hi", "hello world")).to_equal(false)
```

</details>

#### returns false for empty haystack

- returns false for empty haystack
   - Expected: contains("", "x") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns false for empty haystack")
expect(contains("", "x")).to_equal(false)
```

</details>

#### edge cases

#### finds empty needle

- finds empty needle
   - Expected: contains("hello", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds empty needle")
expect(contains("hello", "")).to_equal(true)
```

</details>

#### handles single char needle

- handles single char needle
   - Expected: contains("abc", "b") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles single char needle")
expect(contains("abc", "b")).to_equal(true)
```

</details>

#### handles single char miss

- handles single char miss
   - Expected: contains("abc", "z") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles single char miss")
expect(contains("abc", "z")).to_equal(false)
```

</details>

#### handles repeated pattern

- handles repeated pattern
   - Expected: contains("aaabaaab", "aaab") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles repeated pattern")
expect(contains("aaabaaab", "aaab")).to_equal(true)
```

</details>

### starts_with

#### matches

#### matches prefix

- matches prefix
   - Expected: starts_with("trace32 encrypted", "trace32") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches prefix")
expect(starts_with("trace32 encrypted", "trace32")).to_equal(true)
```

</details>

#### matches full string

- matches full string
   - Expected: starts_with("hello", "hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches full string")
expect(starts_with("hello", "hello")).to_equal(true)
```

</details>

#### matches empty prefix

- matches empty prefix
   - Expected: starts_with("anything", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("matches empty prefix")
expect(starts_with("anything", "")).to_equal(true)
```

</details>

#### no matches

#### rejects wrong prefix

- rejects wrong prefix
   - Expected: starts_with("hello", "world") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects wrong prefix")
expect(starts_with("hello", "world")).to_equal(false)
```

</details>

#### rejects longer prefix

- rejects longer prefix
   - Expected: starts_with("hi", "hello") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects longer prefix")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7180f592518499862664667945e6bb963ae0cee703c0c0c303b866864f6a0184`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7180f592518499862664667945e6bb963ae0cee703c0c0c303b866864f6a0184`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7180f592518499862664667945e6bb963ae0cee703c0c0c303b866864f6a0184`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/cmm_lsp/bulk_validate_spec.spl
mirror: doc/06_spec/feature/usage/cmm_lsp/bulk_validate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cmm_lsp/bulk_validate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cmm_lsp/bulk_validate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cmm_lsp/bulk_validate_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns identity for clean paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/bulk_validate_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns identity for relative clean paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/bulk_validate_spec.spl:156:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns identity for root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
