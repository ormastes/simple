# Feature Db Specification

> Tests covering Feature Database Module, filename extraction, SPipe file detection, filter for SPipe files, failed test detection, error option check, filter failed results, map to extract paths, Result handling, match on Result for error, list append, counter increment, string formatting, struct construction with error, filter and map chain.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Db Specification

## Scenarios

### Feature Database Module

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
val path = "test/unit/example_spec.spl"
val parts = path.split("/")
val filename = parts[parts.len() - 1]
expect filename == "example_spec.spl"
```

</details>

#### handles path without directory

- handles path without directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles path without directory")
val path = "example_spec.spl"
val parts = path.split("/")
val filename = if parts.len() > 0: parts[parts.len() - 1] else: path
expect filename == "example_spec.spl"
```

</details>

### SPipe file detection

#### detects _spec.spl files

- detects _spec.spl files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects _spec.spl files")
val filename = "example_spec.spl"
expect filename.ends_with("_spec.spl") == true
```

</details>

#### rejects non-spec files

- rejects non-spec files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-spec files")
val filename = "example.spl"
expect filename.ends_with("_spec.spl") == false
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
val filename = "example_spec.rs"
expect filename.ends_with("_spec.spl") == false
```

</details>

### filter for SPipe files

#### filters spec files from list

- filters spec files from list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters spec files from list")
val files = ["test_spec.spl", "example.spl", "other_spec.spl"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 2
```

</details>

#### empty list when no specs

- empty list when no specs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty list when no specs")
val files = ["example.spl", "test.rs"]
val specs = files.filter(_1.ends_with("_spec.spl"))
expect specs.len() == 0
```

</details>

### failed test detection

#### detects failed tests

- detects failed tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects failed tests")
val failed_count = 1
expect failed_count > 0 == true
```

</details>

#### detects no failures

- detects no failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects no failures")
val failed_count = 0
expect failed_count > 0 == false
```

</details>

### error option check

#### Some indicates error

- Some indicates error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some indicates error")
val error = Some("error message")
expect error.is_some() == true
```

</details>

#### None indicates no error

- None indicates no error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("None indicates no error")
val error_opt = None
val has_error = false
expect has_error == false
```

</details>

### filter failed results

#### OR condition for failed or error

- OR condition for failed or error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("OR condition for failed or error")
val failed = 1
val has_error = true
expect (failed > 0 or has_error) == true
```

</details>

#### failed but no error

- failed but no error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("failed but no error")
val failed = 1
val has_error = false
expect (failed > 0 or has_error) == true
```

</details>

#### no failed and no error

- no failed and no error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no failed and no error")
val failed = 0
val has_error = false
expect (failed > 0 or has_error) == false
```

</details>

### map to extract paths

#### extracts path field

- extracts path field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts path field")
val paths = ["path1", "path2", "path3"]
expect paths.len() == 3
```

</details>

### Result handling

#### Ok result check

- Ok result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok result check")
expect Ok("updated").is_ok() == true
```

</details>

#### Err result check

- Err result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Err result check")
expect Err("failed").is_err() == true
```

</details>

### match on Result for error

#### matches Err and increments counter

- matches Err and increments counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Err and increments counter")
val result = Err("db error")
val total_failed = 5
val matched = match result:
    Err(e) => total_failed + 1
    Ok(_) => total_failed
expect matched == 6
```

</details>

#### matches Ok and keeps counter

- matches Ok and keeps counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Ok and keeps counter")
val result = Ok("success")
val total_failed = 5
val matched = match result:
    Err(e) => total_failed + 1
    Ok(_) => total_failed
expect matched == 5
```

</details>

### list append

#### adds element to list

- adds element to list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds element to list")
var list = [1, 2, 3]
val new_list = list.append(4)
expect new_list.len() == 4
```

</details>

### counter increment

#### increments total_failed

- increments total_failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments total_failed")
val total_failed = 5
val new_total = total_failed + 1
expect new_total == 6
```

</details>

### string formatting

#### interpolates error message

- interpolates error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates error message")
val e = "database error"
val msg = "feature db update failed: {e}"
expect msg.contains("database error") == true
```

</details>

#### interpolates path

- interpolates path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates path")
val path = "doc/features/feature_db.sdn"
val msg = "Would update {path}"
expect msg.contains("feature_db.sdn") == true
```

</details>

### struct construction with error

#### constructs with Some error

- constructs with Some error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with Some error")
val path = "test.spl"
val error_msg = Some("error")
expect path == "test.spl"
expect error_msg.is_some() == true
```

</details>

### filter and map chain

#### chains filter then map

- chains filter then map


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains filter then map")
val numbers = [1, 2, 3, 4, 5]
val filtered = numbers.filter(_1 > 2)
val mapped = filtered.map(_1 * 2)
expect mapped.len() == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/feature_db_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Feature Database Module, filename extraction, SPipe file detection, filter for SPipe files, failed test detection, error option check, filter failed results, map to extract paths, Result handling, match on Result for error, list append, counter increment, string formatting, struct construction with error, filter and map chain.
- Feature Database Module
- filename extraction
- SPipe file detection
- filter for SPipe files
- failed test detection
- error option check
- filter failed results
- map to extract paths
- Result handling
- match on Result for error
- list append
- counter increment
- string formatting
- struct construction with error
- filter and map chain

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

- Canonical SPipe generation for source `7f120abdefd5e667429bf8be5dd7eee3927d2e15979b7e1bc183b36adc5f09a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f120abdefd5e667429bf8be5dd7eee3927d2e15979b7e1bc183b36adc5f09a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f120abdefd5e667429bf8be5dd7eee3927d2e15979b7e1bc183b36adc5f09a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/feature_db_spec.spl
mirror: doc/06_spec/unit/app/tooling/feature_db_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/feature_db_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/feature_db_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/feature_db_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/feature_db_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts filename from path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/feature_db_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles path without directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
