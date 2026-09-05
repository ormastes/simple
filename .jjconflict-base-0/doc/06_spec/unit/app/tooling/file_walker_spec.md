# File Walker Specification

> Tests covering file_walker module compilation, is_file detection, single file handling, spec file filtering, filename extraction, summary calculations, modified count check, string interpolation in summary, conditional print, extension check, list construction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Walker Specification

## Scenarios

### file_walker module compilation

#### compiles successfully

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles successfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles successfully")
expect 1 + 1 == 2
```

</details>

### is_file detection

#### detects file with extension

- detects file with extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects file with extension")
val path = "test.spl"
val has_ext = path.contains(".")
expect has_ext == true
```

</details>

#### detects directory without extension

- detects directory without extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects directory without extension")
val path = "src"
val has_ext = path.contains(".")
expect has_ext == false
```

</details>

#### detects file in path

- detects file in path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects file in path")
val path = "src/test.spl"
val has_ext = path.contains(".")
expect has_ext == true
```

</details>

### single file handling

#### returns single file as list

- returns single file as list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single file as list")
val path = "test.spl"
val is_single_file = true
val result = if is_single_file: [path] else: []
expect result.len() == 1
```

</details>

#### returns directory walk result

- returns directory walk result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns directory walk result")
val is_single_file = false
val files = ["file1.spl", "file2.spl"]
val result = if is_single_file: [] else: files
expect result.len() == 2
```

</details>

### spec file filtering

#### filters _spec.spl files

- filters _spec.spl files


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters _spec.spl files")
val files = ["test_spec.spl", "example.spl", "other_spec.spl"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 2
```

</details>

#### no specs in list

- no specs in list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no specs in list")
val files = ["test.spl", "example.spl"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 0
```

</details>

#### all files are specs

- all files are specs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all files are specs")
val files = ["test_spec.spl", "example_spec.spl"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 2
```

</details>

### filename extraction

#### extracts filename from path

- extracts filename from path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts filename from path")
val path = "src/test/example.spl"
val parts = path.split("/")
val filename = parts[parts.len() - 1]
expect filename == "example.spl"
```

</details>

#### handles filename without directory

- handles filename without directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles filename without directory")
val path = "example.spl"
val parts = path.split("/")
val filename = if parts.len() > 0: parts[parts.len() - 1] else: path
expect filename == "example.spl"
```

</details>

### summary calculations

#### calculates unchanged count

- calculates unchanged count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates unchanged count")
val total = 10
val modified = 3
val errors = 1
val unchanged = total - modified - errors
expect unchanged == 6
```

</details>

#### no errors

- no errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no errors")
val total = 10
val modified = 5
val errors = 0
val unchanged = total - modified - errors
expect unchanged == 5
```

</details>

#### all modified

- all modified


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all modified")
val total = 5
val modified = 5
val errors = 0
val unchanged = total - modified - errors
expect unchanged == 0
```

</details>

### modified count check

#### has modifications

- has modifications


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has modifications")
val modified = 3
expect modified > 0 == true
```

</details>

#### no modifications

- no modifications


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no modifications")
val modified = 0
expect modified > 0 == false
```

</details>

### string interpolation in summary

#### interpolates modified count

- interpolates modified count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates modified count")
val count = 5
val msg = "  Would modify: {count}"
expect msg.contains("5") == true
```

</details>

#### interpolates unchanged count

- interpolates unchanged count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates unchanged count")
val unchanged = 3
val msg = "  Unchanged: {unchanged}"
expect msg.contains("3") == true
```

</details>

#### interpolates errors

- interpolates errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates errors")
val errors = 2
val msg = "  Errors: {errors}"
expect msg.contains("2") == true
```

</details>

### conditional print

#### prints additional message when modified

- prints additional message when modified


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prints additional message when modified")
val modified = 3
val should_print = modified > 0
expect should_print == true
```

</details>

#### no additional message when zero

- no additional message when zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no additional message when zero")
val modified = 0
val should_print = modified > 0
expect should_print == false
```

</details>

### extension check

#### checks .spl extension

- checks .spl extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks .spl extension")
val filename = "test.spl"
expect filename.ends_with(".spl") == true
```

</details>

#### rejects other extensions

- rejects other extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects other extensions")
val filename = "test.rs"
expect filename.ends_with(".spl") == false
```

</details>

### list construction

#### single element list

- single element list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single element list")
val path = "test.spl"
val list = [path]
expect list.len() == 1
```

</details>

#### empty list

- empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty list")
val list = []
expect list.len() == 0
```

</details>

#### multi-element list

- multi-element list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-element list")
val list = ["a.spl", "b.spl", "c.spl"]
expect list.len() == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/file_walker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering file_walker module compilation, is_file detection, single file handling, spec file filtering, filename extraction, summary calculations, modified count check, string interpolation in summary, conditional print, extension check, list construction.
- file_walker module compilation
- is_file detection
- single file handling
- spec file filtering
- filename extraction
- summary calculations
- modified count check
- string interpolation in summary
- conditional print
- extension check
- list construction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `358a493bc27bf6b328a93fb893e0933a44d8293e40ec3ecd56774b37437b90c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `358a493bc27bf6b328a93fb893e0933a44d8293e40ec3ecd56774b37437b90c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `358a493bc27bf6b328a93fb893e0933a44d8293e40ec3ecd56774b37437b90c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/file_walker_spec.spl
mirror: doc/06_spec/unit/app/tooling/file_walker_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/file_walker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/file_walker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/file_walker_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/file_walker_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects file with extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/file_walker_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects directory without extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
