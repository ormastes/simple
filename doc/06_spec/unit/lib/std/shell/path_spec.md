# path_spec

> Feature: Path Manipulation

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# path_spec

Feature: Path Manipulation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/shell/path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Path Manipulation
Category: Filesystem
Status: Active

## Scenarios

### Path Manipulation

#### basename

#### should extract filename from path

- should extract filename from path
   - Expected: result equals `file.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should extract filename from path")
val result = path_basename("/home/user/file.txt")
expect(result).to_equal("file.txt")
```

</details>

#### should handle path with no directory

- should handle path with no directory
   - Expected: result equals `file.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle path with no directory")
val result = path_basename("file.txt")
expect(result).to_equal("file.txt")
```

</details>

#### should handle directory path

- should handle directory path
   - Expected: result equals `dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle directory path")
val result = path_basename("/home/user/dir/")
expect(result).to_equal("dir")
```

</details>

#### should handle root path

- should handle root path
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle root path")
val result = path_basename("/")
expect(result).to_equal("")
```

</details>

#### should handle empty path

- should handle empty path
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle empty path")
val result = path_basename("")
expect(result).to_equal("")
```

</details>

#### dirname

#### should extract directory from path

- should extract directory from path
   - Expected: result equals `/home/user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should extract directory from path")
val result = path_dirname("/home/user/file.txt")
expect(result).to_equal("/home/user")
```

</details>

#### should handle path with single directory

- should handle path with single directory
   - Expected: result equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle path with single directory")
val result = path_dirname("/file.txt")
expect(result).to_equal("/")
```

</details>

#### should handle relative path

- should handle relative path
   - Expected: result equals `dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle relative path")
val result = path_dirname("dir/file.txt")
expect(result).to_equal("dir")
```

</details>

#### should handle file with no directory

- should handle file with no directory
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle file with no directory")
val result = path_dirname("file.txt")
expect(result).to_equal("")
```

</details>

#### should handle empty path

- should handle empty path
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle empty path")
val result = path_dirname("")
expect(result).to_equal("")
```

</details>

#### extension

#### should extract file extension

- should extract file extension
   - Expected: result equals `txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should extract file extension")
val result = path_ext("/home/user/file.txt")
expect(result).to_equal("txt")
```

</details>

#### should handle multiple dots

- should handle multiple dots
   - Expected: result equals `gz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle multiple dots")
val result = path_ext("file.tar.gz")
expect(result).to_equal("gz")
```

</details>

#### should handle no extension

- should handle no extension
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle no extension")
val result = path_ext("/home/user/file")
expect(result).to_equal("")
```

</details>

#### should handle hidden file with extension

- should handle hidden file with extension
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle hidden file with extension")
val result = path_ext(".bashrc")
expect(result).to_equal("")
```

</details>

#### should handle hidden file with dot and extension

- should handle hidden file with dot and extension
   - Expected: result equals `json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle hidden file with dot and extension")
val result = path_ext(".config.json")
expect(result).to_equal("json")
```

</details>

#### is_absolute

#### should detect absolute path

- should detect absolute path
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should detect absolute path")
val result = path_is_absolute("/tmp")
expect(result).to_equal(true)
```

</details>

#### should detect relative path

- should detect relative path
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should detect relative path")
val result = path_is_absolute("relative/path")
expect(result).to_equal(false)
```

</details>

#### should handle current directory as relative

- should handle current directory as relative
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle current directory as relative")
val result = path_is_absolute(".")
expect(result).to_equal(false)
```

</details>

#### should handle parent directory as relative

- should handle parent directory as relative
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle parent directory as relative")
val result = path_is_absolute("..")
expect(result).to_equal(false)
```

</details>

#### join

#### should join path components

- should join path components
   - Expected: result equals `home/user/file.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should join path components")
val result = path_join_many(["home", "user", "file.txt"])
expect(result).to_equal("home/user/file.txt")
```

</details>

#### should handle single component

- should handle single component
   - Expected: result equals `home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle single component")
val result = path_join_many(["home"])
expect(result).to_equal("home")
```

</details>

#### should handle empty list

- should handle empty list
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle empty list")
val result = path_join_many([])
expect(result).to_equal("")
```

</details>

#### should not add separator if already present

- should not add separator if already present
   - Expected: result equals `home/user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not add separator if already present")
val result = path_join_two("home/", "user")
expect(result).to_equal("home/user")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `0a5fdb88c01579b36983bc514d8cdb67c02df53954528e6050e41d3323ac8943`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a5fdb88c01579b36983bc514d8cdb67c02df53954528e6050e41d3323ac8943`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a5fdb88c01579b36983bc514d8cdb67c02df53954528e6050e41d3323ac8943`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/std/shell/path_spec.spl
mirror: doc/06_spec/unit/lib/std/shell/path_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/shell/path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/shell/path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/shell/path_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract filename from path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/path_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract filename from path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/shell/path_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle path with no directory' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/path_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle path with no directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/shell/path_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle directory path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/path_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle directory path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/shell/path_spec.spl:114:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle root path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/path_spec.spl:120:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle empty path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/std/shell/path_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract directory from path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
