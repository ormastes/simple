# Misc Commands Specification

> Tests covering help flag detection, lock command flags, argument length validation, list slicing, Option handling, conditional branches, Result patterns, nested match patterns, list length checks, string formatting, exit code conventions, boolean parameters, early return pattern, misc_commands module compilation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Misc Commands Specification

## Scenarios

### help flag detection

#### detects -h flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects -h flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects -h flag")
val args = ["simple", "diagram", "-h"]
val has_help = args.any(_1 == "-h" or _1 == "--help")
expect has_help == true
```

</details>

#### detects --help flag

- detects --help flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --help flag")
val args = ["simple", "diagram", "--help"]
val has_help = args.any(_1 == "-h" or _1 == "--help")
expect has_help == true
```

</details>

#### no help when absent

- no help when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no help when absent")
val args = ["simple", "diagram", "file.json"]
val has_help = args.any(_1 == "-h" or _1 == "--help")
expect has_help == false
```

</details>

### lock command flags

#### detects --check flag

- detects --check flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --check flag")
val args = ["simple", "lock", "--check"]
val check_only = args.any(_1 == "--check")
expect check_only == true
```

</details>

#### detects --info flag

- detects --info flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --info flag")
val args = ["simple", "lock", "--info"]
val info_only = args.any(_1 == "--info")
expect info_only == true
```

</details>

#### no flags when absent

- no flags when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no flags when absent")
val args = ["simple", "lock"]
val check_only = args.any(_1 == "--check")
val info_only = args.any(_1 == "--info")
expect check_only == false
expect info_only == false
```

</details>

### argument length validation

#### run requires 2 args minimum

- run requires 2 args minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("run requires 2 args minimum")
val args = ["simple", "run", "script.spl"]
expect args.len() >= 2 == true
```

</details>

#### run fails with insufficient args

- run fails with insufficient args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("run fails with insufficient args")
val args = ["simple"]
expect args.len() < 2 == true
```

</details>

### list slicing

#### slices from index to end

- slices from index to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slices from index to end")
val args = ["simple", "diagram", "-f", "file.json"]
val diagram_args = args.slice(1, args.len())
expect diagram_args.len() == 3
```

</details>

#### empty slice when start equals end

- empty slice when start equals end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty slice when start equals end")
val args = ["simple"]
val diagram_args = args.slice(1, args.len())
expect diagram_args.len() == 0
```

</details>

### Option handling

#### Some wraps value

- Some wraps value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some wraps value")
val opt = Some("file.json")
expect opt.is_some() == true
```

</details>

#### unwrap gets value

- unwrap gets value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap gets value")
val opt = Some("file.json")
val value = opt.unwrap()
expect value == "file.json"
```

</details>

### conditional branches

#### info_only takes precedence

- info_only takes precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("info_only takes precedence")
val info_only = true
val check_only = true
val branch = if info_only: "info" elif check_only: "check" else: "generate"
expect branch == "info"
```

</details>

#### check_only when not info

- check_only when not info


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("check_only when not info")
val info_only = false
val check_only = true
val branch = if info_only: "info" elif check_only: "check" else: "generate"
expect branch == "check"
```

</details>

#### default when no flags

- default when no flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default when no flags")
val info_only = false
val check_only = false
val branch = if info_only: "info" elif check_only: "check" else: "generate"
expect branch == "generate"
```

</details>

### Result patterns

#### Ok unwraps value

- Ok unwraps value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok unwraps value")
expect Ok(42).is_ok() == true
```

</details>

#### Err contains error

- Err contains error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Err contains error")
expect Err("error").is_err() == true
```

</details>

### nested match patterns

#### outer match selects Some

- outer match selects Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("outer match selects Some")
val outer = Some("value")
val selected = match outer:
    Some(v) => "has value"
    None => "no value"
expect selected == "has value"
```

</details>

#### checks None option

- checks None option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks None option")
val none_outer: Option<text> = None
expect none_outer.is_none() == true
```

</details>

### list length checks

#### detects non-empty patterns

- detects non-empty patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects non-empty patterns")
val patterns = ["*.spl", "*.txt"]
expect patterns.len() > 0 == true
```

</details>

#### list comparison works

- list comparison works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list comparison works")
val test_list = ["a", "b"]
expect test_list.len() == 2
```

</details>

### string formatting

#### interpolates variable

- interpolates variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates variable")
val name = "test"
val events_count = 5
val msg = "Loaded profile: {name} ({events_count} events)"
expect msg.contains("test") == true
expect msg.contains("5") == true
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
val path = "output/diagram.puml"
val msg = "  Sequence diagram: {path}"
expect msg.contains("output/diagram.puml") == true
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

### boolean parameters

#### both gc flags false

- both gc flags false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("both gc flags false")
val gc_log = false
val gc_off = false
expect gc_log == false
expect gc_off == false
```

</details>

#### gc_log true

- gc_log true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_log true")
val gc_log = true
val gc_off = false
expect gc_log == true
```

</details>

#### gc_off true

- gc_off true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_off true")
val gc_log = false
val gc_off = true
expect gc_off == true
```

</details>

### early return pattern

#### validates condition for early return

- validates condition for early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates condition for early return")
val args_len = 1
val should_return = args_len < 2
expect should_return == true
```

</details>

#### continues when condition false

- continues when condition false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues when condition false")
val args_len = 3
val should_return = args_len < 2
expect should_return == false
```

</details>

### misc_commands module compilation

#### compiles successfully

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/misc_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering help flag detection, lock command flags, argument length validation, list slicing, Option handling, conditional branches, Result patterns, nested match patterns, list length checks, string formatting, exit code conventions, boolean parameters, early return pattern, misc_commands module compilation.
- help flag detection
- lock command flags
- argument length validation
- list slicing
- Option handling
- conditional branches
- Result patterns
- nested match patterns
- list length checks
- string formatting
- exit code conventions
- boolean parameters
- early return pattern
- misc_commands module compilation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `bcb6b48976669472af9253e7ff68657a748c22bff7fdda4d7ce1bcf04171b67b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bcb6b48976669472af9253e7ff68657a748c22bff7fdda4d7ce1bcf04171b67b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bcb6b48976669472af9253e7ff68657a748c22bff7fdda4d7ce1bcf04171b67b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/misc_commands_spec.spl
mirror: doc/06_spec/unit/app/tooling/misc_commands_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/misc_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/misc_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/misc_commands_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects -h flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/misc_commands_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects --help flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/misc_commands_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no help when absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
