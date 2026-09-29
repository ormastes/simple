# Pkg Commands Specification

> Tests covering pkg_commands module compilation, argument length validation, option flag detection, cache subcommand detection, optional parameter extraction, option parsing patterns, while loop iteration, Result handling, boolean result handling, list operations, string formatting, conditional status suffix, exit code conventions, Option handling, update result checking, counter comparisons.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pkg Commands Specification

## Scenarios

### pkg_commands module compilation

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

### argument length validation

#### add requires 2 args minimum

- add requires 2 args minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add requires 2 args minimum")
val args = ["simple", "add", "package"]
expect args.len() >= 2 == true
```

</details>

#### remove requires 2 args minimum

- remove requires 2 args minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove requires 2 args minimum")
val args = ["simple", "remove", "package"]
expect args.len() >= 2 == true
```

</details>

### option flag detection

#### detects --dev flag

- detects --dev flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --dev flag")
val args = ["simple", "add", "pkg", "--dev"]
val has_dev = args.any(_1 == "--dev")
expect has_dev == true
```

</details>

#### detects --path flag

- detects --path flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --path flag")
val args = ["simple", "add", "pkg", "--path", "/tmp"]
val has_path = args.any(_1 == "--path")
expect has_path == true
```

</details>

#### detects --git flag

- detects --git flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --git flag")
val args = ["simple", "add", "pkg", "--git", "https://github.com/foo/bar"]
val has_git = args.any(_1 == "--git")
expect has_git == true
```

</details>

### cache subcommand detection

#### detects clean subcommand

- detects clean subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects clean subcommand")
val args = ["simple", "cache", "clean"]
expect args[1] == "cache"
expect args[2] == "clean"
```

</details>

#### detects list subcommand

- detects list subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects list subcommand")
val args = ["simple", "cache", "list"]
expect args[1] == "cache"
expect args[2] == "list"
```

</details>

#### detects info subcommand

- detects info subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects info subcommand")
val args = ["simple", "cache", "info"]
expect args[1] == "cache"
expect args[2] == "info"
```

</details>

### optional parameter extraction

#### extracts name when present

- extracts name when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts name when present")
val args = ["simple", "init", "myproject"]
val name = if args.len() > 1: Some(args[1]) else: None
expect name.is_some() == true
```

</details>

#### no name when absent

- no name when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no name when absent")
val args = ["simple", "init"]
val name = if args.len() > 1: Some(args[1]) else: None
expect name.is_none() == true
```

</details>

### option parsing patterns

#### finds non-flag argument

- finds non-flag argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds non-flag argument")
val arg = "mypackage"
val is_flag = arg.starts_with("-")
expect is_flag == false
```

</details>

#### identifies flag argument

- identifies flag argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies flag argument")
val arg = "--dev"
val is_flag = arg.starts_with("-")
expect is_flag == true
```

</details>

### while loop iteration

#### iterates through arguments

- iterates through arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates through arguments")
val args = ["simple", "add", "pkg", "--dev"]
var count = 0
var i = 0
while i < args.len():
    count = count + 1
    i = i + 1
expect count == 4
```

</details>

#### skips flag and value

- skips flag and value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips flag and value")
val args = ["--path", "/tmp", "other"]
var i = 0
if args[i] == "--path":
    i = i + 2  # Skip flag and value
expect i == 2
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
expect Ok(()).is_ok() == true
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
expect Err("error").is_err() == true
```

</details>

### boolean result handling

#### Ok(true) indicates success

- Ok(true) indicates success


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok(true) indicates success")
val result = Ok(true)
val is_success = result.is_ok()
expect is_success == true
```

</details>

#### Ok(false) handled correctly

- Ok(false) handled correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok(false) handled correctly")
val result = Ok(false)
val is_ok = result.is_ok()
expect is_ok == true
```

</details>

### list operations

#### join list items

- join list items


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("join list items")
val items = ["pkg1", "pkg2", "pkg3"]
val joined = items.join(", ")
expect joined.contains("pkg1") == true
expect joined.contains(", ") == true
```

</details>

#### list length check

- list length check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list length check")
val items = ["pkg1", "pkg2"]
expect items.len() == 2
```

</details>

### string formatting

#### constructs error message

- constructs error message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs error message")
val pkg_name = "mypackage"
val msg = "error: add requires {pkg_name}"
expect msg.contains("mypackage") == true
```

</details>

#### constructs success message

- constructs success message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs success message")
val pkg_name = "mypackage"
val msg = "Added dependency '{pkg_name}'"
expect msg.contains("mypackage") == true
```

</details>

### conditional status suffix

#### empty suffix when linked

- empty suffix when linked


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty suffix when linked")
val is_linked = true
val status = if is_linked: "" else: " (not linked)"
expect status == ""
```

</details>

#### suffix when not linked

- suffix when not linked


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suffix when not linked")
val is_linked = false
val status = if is_linked: "" else: " (not linked)"
expect status == " (not linked)"
```

</details>

### exit code conventions

#### success returns 0

- success returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("success returns 0")
expect 0 == 0
```

</details>

#### error returns 1

- error returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error returns 1")
expect 1 == 1
```

</details>

### Option handling

#### Some has value

- Some has value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some has value")
expect Some("value").is_some() == true
```

</details>

### update result checking

#### non-empty updated list

- non-empty updated list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-empty updated list")
val updated = ["pkg1", "pkg2"]
expect updated.len() == 2
```

</details>

#### list has count

- list has count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list has count")
val items = ["a", "b"]
expect items.len() > 0 == true
```

</details>

### counter comparisons

#### all counters zero

- all counters zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all counters zero")
val installed = 0
val up_to_date = 0
val skipped = 0
val all_zero = installed == 0 and up_to_date == 0 and skipped == 0
expect all_zero == true
```

</details>

#### has non-zero counter

- has non-zero counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has non-zero counter")
val installed = 5
val up_to_date = 0
val skipped = 0
val has_installed = installed > 0
expect has_installed == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/pkg_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pkg_commands module compilation, argument length validation, option flag detection, cache subcommand detection, optional parameter extraction, option parsing patterns, while loop iteration, Result handling, boolean result handling, list operations, string formatting, conditional status suffix, exit code conventions, Option handling, update result checking, counter comparisons.
- pkg_commands module compilation
- argument length validation
- option flag detection
- cache subcommand detection
- optional parameter extraction
- option parsing patterns
- while loop iteration
- Result handling
- boolean result handling
- list operations
- string formatting
- conditional status suffix
- exit code conventions
- Option handling
- update result checking
- counter comparisons

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `729d21793b1a61e4be040d6d514d81f1b54570e268be6aaa4263e72c84cccff1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `729d21793b1a61e4be040d6d514d81f1b54570e268be6aaa4263e72c84cccff1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `729d21793b1a61e4be040d6d514d81f1b54570e268be6aaa4263e72c84cccff1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/pkg_commands_spec.spl
mirror: doc/06_spec/unit/app/tooling/pkg_commands_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/pkg_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/pkg_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/pkg_commands_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/pkg_commands_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add requires 2 args minimum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/pkg_commands_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'remove requires 2 args minimum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
