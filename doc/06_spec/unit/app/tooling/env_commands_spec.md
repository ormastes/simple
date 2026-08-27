# Env Commands Specification

> Tests covering env_commands module compilation, subcommand detection, argument length validation, force flag detection, optional shell parameter, subcommand extraction, exit code conventions, error message format, help text formatting, name parameter extraction, match pattern validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Env Commands Specification

## Scenarios

### env_commands module compilation

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

### subcommand detection

#### detects create subcommand

- detects create subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects create subcommand")
val cmd = "create"
expect cmd == "create"
```

</details>

#### detects activate subcommand

- detects activate subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects activate subcommand")
val cmd = "activate"
expect cmd == "activate"
```

</details>

#### detects list subcommand

- detects list subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects list subcommand")
val cmd = "list"
expect cmd == "list"
```

</details>

#### detects remove subcommand

- detects remove subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects remove subcommand")
val cmd = "remove"
expect cmd == "remove"
```

</details>

#### detects info subcommand

- detects info subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects info subcommand")
val cmd = "info"
expect cmd == "info"
```

</details>

### argument length validation

#### create requires 3 args minimum

- create requires 3 args minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create requires 3 args minimum")
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### activate requires 3 args minimum

- activate requires 3 args minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("activate requires 3 args minimum")
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### remove requires 3 args minimum

- remove requires 3 args minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove requires 3 args minimum")
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### info requires 3 args minimum

- info requires 3 args minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("info requires 3 args minimum")
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### list requires only 2 args

- list requires only 2 args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list requires only 2 args")
val args = ["simple", "env"]
expect args.len() >= 2 == true
```

</details>

### force flag detection

#### detects --force flag

- detects --force flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --force flag")
val args = ["simple", "env", "remove", "myenv", "--force"]
val has_force = args.any(_1 == "--force")
expect has_force == true
```

</details>

#### no force flag when absent

- no force flag when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no force flag when absent")
val args = ["simple", "env", "remove", "myenv"]
val has_force = args.any(_1 == "--force")
expect has_force == false
```

</details>

### optional shell parameter

#### detects shell when present

- detects shell when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects shell when present")
val args = ["simple", "env", "activate", "myenv", "bash"]
val has_shell = args.len() > 3
expect has_shell == true
```

</details>

#### no shell when absent

- no shell when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no shell when absent")
val args = ["simple", "env", "activate", "myenv"]
val has_shell = args.len() > 3
expect has_shell == false
```

</details>

### subcommand extraction

#### extracts subcommand from index 1

- extracts subcommand from index 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts subcommand from index 1")
val args = ["simple", "env", "create", "name"]
val subcommand = if args.len() > 1:
    Some(args[1])
else:
    None
expect subcommand.is_some() == true
```

</details>

#### returns None when no subcommand

- returns None when no subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None when no subcommand")
val args = ["simple"]
val subcommand = if args.len() > 1:
    Some(args[1])
else:
    None
expect subcommand.is_none() == true
```

</details>

### exit code conventions

#### success returns 0

- success returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("success returns 0")
val exit_code = 0
expect exit_code == 0
```

</details>

#### error returns 1

- error returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error returns 1")
val exit_code = 1
expect exit_code == 1
```

</details>

### error message format

#### error prefix format

- error prefix format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error prefix format")
val msg = "error: env create requires a name"
expect msg.starts_with("error:") == true
```

</details>

#### usage prefix format

- usage prefix format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("usage prefix format")
val msg = "Usage: simple env create <name>"
expect msg.starts_with("Usage:") == true
```

</details>

### help text formatting

#### validates command examples

- validates command examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates command examples")
val example = "simple env create <name>"
expect example.contains("env") == true
expect example.contains("create") == true
```

</details>

#### validates help structure

- validates help structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates help structure")
val header = "Simple Environment Management"
expect header.contains("Environment") == true
```

</details>

### name parameter extraction

#### extracts name from index 2

- extracts name from index 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts name from index 2")
val args = ["simple", "env", "create", "myenv"]
val name = args[2]
expect name == "myenv"
```

</details>

#### handles different names

- handles different names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles different names")
val args = ["simple", "env", "activate", "testenv"]
val name = args[2]
expect name == "testenv"
```

</details>

### match pattern validation

#### matches create variant

- matches create variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches create variant")
val cmd = Some("create")
val is_create = match cmd:
    Some("create") => true
    _ => false
expect is_create == true
```

</details>

#### matches None variant

- matches None variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches None variant")
val cmd: Option<text> = None
val is_none = match cmd:
    None => true
    _ => false
expect is_none == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/env_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering env_commands module compilation, subcommand detection, argument length validation, force flag detection, optional shell parameter, subcommand extraction, exit code conventions, error message format, help text formatting, name parameter extraction, match pattern validation.
- env_commands module compilation
- subcommand detection
- argument length validation
- force flag detection
- optional shell parameter
- subcommand extraction
- exit code conventions
- error message format
- help text formatting
- name parameter extraction
- match pattern validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `45cb0901ef743af3c61ba5fbbc1998f5c8d85ca74b6a778245530fb94b012759`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45cb0901ef743af3c61ba5fbbc1998f5c8d85ca74b6a778245530fb94b012759`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45cb0901ef743af3c61ba5fbbc1998f5c8d85ca74b6a778245530fb94b012759`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/env_commands_spec.spl
mirror: doc/06_spec/unit/app/tooling/env_commands_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/env_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/env_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/env_commands_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/env_commands_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects create subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/env_commands_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects activate subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
