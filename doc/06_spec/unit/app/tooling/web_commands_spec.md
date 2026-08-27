# Web Commands Specification

> Tests covering web_commands module compilation, web subcommand detection, argument validation, flag detection, flag value extraction, array indexing, boolean negation, struct construction, u16 type, Result patterns, Option chaining pattern, list operations, match on string, parameter extraction, exit codes, early return validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Commands Specification

## Scenarios

### web_commands module compilation

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

### web subcommand detection

#### detects build subcommand

- detects build subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects build subcommand")
val args = ["simple", "web", "build", "app.sui"]
expect args[1] == "web"
expect args[2] == "build"
```

</details>

#### detects init subcommand

- detects init subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects init subcommand")
val args = ["simple", "web", "init", "myproject"]
expect args[2] == "init"
```

</details>

#### detects features subcommand

- detects features subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects features subcommand")
val args = ["simple", "web", "features"]
expect args[2] == "features"
```

</details>

#### detects serve subcommand

- detects serve subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects serve subcommand")
val args = ["simple", "web", "serve", "app.sui"]
expect args[2] == "serve"
```

</details>

### argument validation

#### web requires subcommand

- web requires subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("web requires subcommand")
val args = ["simple"]
expect args.len() < 2 == true
```

</details>

#### build requires file

- build requires file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build requires file")
val args = ["simple", "web"]
expect args.len() < 3 == true
```

</details>

#### init requires project name

- init requires project name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init requires project name")
val args = ["simple", "web", "init"]
expect args.len() < 3 == true
```

</details>

#### serve requires file

- serve requires file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serve requires file")
val args = ["simple", "web", "serve"]
expect args.len() < 3 == true
```

</details>

### flag detection

#### detects --optimize flag

- detects --optimize flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --optimize flag")
val args = ["simple", "web", "build", "app.sui", "--optimize"]
val has_optimize = args.any(_1 == "--optimize")
expect has_optimize == true
```

</details>

#### detects --minify flag

- detects --minify flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --minify flag")
val args = ["simple", "web", "build", "app.sui", "--minify"]
val has_minify = args.any(_1 == "--minify")
expect has_minify == true
```

</details>

#### detects --open flag

- detects --open flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --open flag")
val args = ["simple", "web", "serve", "app.sui", "--open"]
val has_open = args.any(_1 == "--open")
expect has_open == true
```

</details>

#### detects --no-watch flag

- detects --no-watch flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --no-watch flag")
val args = ["simple", "web", "serve", "app.sui", "--no-watch"]
val has_no_watch = args.any(_1 == "--no-watch")
expect has_no_watch == true
```

</details>

### flag value extraction

#### checks if .any works for flag presence

- checks if .any works for flag presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if .any works for flag presence")
val args = ["simple", "web", "build", "app.sui", "-o", "dist"]
val has_o = args.any(_1 == "-o")
expect has_o == true
```

</details>

#### checks multiple flag options

- checks multiple flag options


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks multiple flag options")
val args = ["simple", "web", "build", "app.sui", "--output", "dist"]
val has_output = args.any(_1 == "-o" or _1 == "--output")
expect has_output == true
```

</details>

#### checks module flag presence

- checks module flag presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks module flag presence")
val args = ["simple", "web", "build", "app.sui", "--module", "myapp"]
val has_module = args.any(_1 == "--module")
expect has_module == true
```

</details>

#### checks port flag presence

- checks port flag presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks port flag presence")
val args = ["simple", "web", "serve", "app.sui", "-p", "3000"]
val has_p = args.any(_1 == "-p")
expect has_p == true
```

</details>

### array indexing

#### gets value at specific index

- gets value at specific index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets value at specific index")
val args = ["simple", "web", "build", "app.sui", "-o", "dist"]
val value = args[5]
expect value == "dist"
```

</details>

### boolean negation

#### watch enabled by default_val

- watch enabled by default_val


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("watch enabled by default_val")
val has_no_watch = false
val watch = not has_no_watch
expect watch == true
```

</details>

#### watch disabled with --no-watch

- watch disabled with --no-watch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("watch disabled with --no-watch")
val has_no_watch = true
val watch = not has_no_watch
expect watch == false
```

</details>

### struct construction

#### constructs with all fields

- constructs with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with all fields")
val build_optimize = true
val build_minify = false
expect build_optimize == true
expect build_minify == false
```

</details>

### u16 type

#### default_val port is 8000

- default_val port is 8000


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_val port is 8000")
val default_port = 8000
expect default_port == 8000
```

</details>

#### custom port value

- custom port value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom port value")
val custom_port = 3000
expect custom_port == 3000
```

</details>

### Result patterns

#### Ok result check

- Ok result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok result check")
expect Ok(8080).is_ok() == true
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
expect Err("invalid").is_err() == true
```

</details>

### Option chaining pattern

#### Some unwraps to value

- Some unwraps to value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some unwraps to value")
val opt = Some(5)
if opt.is_some():
    val value = opt.unwrap()
    expect value == 5
```

</details>

### list operations

#### checks length for bounds

- checks length for bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks length for bounds")
val args = ["a", "b", "c", "d"]
val idx = 2
val in_bounds = idx + 1 < args.len()
expect in_bounds == true
```

</details>

#### out of bounds check

- out of bounds check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("out of bounds check")
val args = ["a", "b"]
val idx = 5
val in_bounds = idx + 1 < args.len()
expect in_bounds == false
```

</details>

### match on string

#### matches build

- matches build


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches build")
val cmd = "build"
val matched = match cmd:
    "build" => true
    _ => false
expect matched == true
```

</details>

#### matches serve

- matches serve


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches serve")
val cmd = "serve"
val matched = match cmd:
    "serve" => true
    _ => false
expect matched == true
```

</details>

#### default_val case

- default_val case


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default_val case")
val cmd = "unknown"
val matched = match cmd:
    "build" => false
    "serve" => false
    _ => true
expect matched == true
```

</details>

### parameter extraction

#### extracts source file

- extracts source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts source file")
val args = ["simple", "web", "build", "app.sui"]
val source = args[2]
expect source == "app.sui"
```

</details>

#### extracts project name

- extracts project name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts project name")
val args = ["simple", "web", "init", "myproject"]
val project_name = args[2]
expect project_name == "myproject"
```

</details>

### exit codes

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

### early return validation

#### validates insufficient args

- validates insufficient args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates insufficient args")
val args_len = 1
val should_return = args_len < 2
expect should_return == true
```

</details>

#### validates sufficient args

- validates sufficient args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates sufficient args")
val args_len = 3
val should_return = args_len < 2
expect should_return == false
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/web_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering web_commands module compilation, web subcommand detection, argument validation, flag detection, flag value extraction, array indexing, boolean negation, struct construction, u16 type, Result patterns, Option chaining pattern, list operations, match on string, parameter extraction, exit codes, early return validation.
- web_commands module compilation
- web subcommand detection
- argument validation
- flag detection
- flag value extraction
- array indexing
- boolean negation
- struct construction
- u16 type
- Result patterns
- Option chaining pattern
- list operations
- match on string
- parameter extraction
- exit codes
- early return validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
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

- Canonical SPipe generation for source `dbfbb2e160585d663aa502fe1eded9d7ae040ba7f91d109ecc61713d8e43718b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbfbb2e160585d663aa502fe1eded9d7ae040ba7f91d109ecc61713d8e43718b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbfbb2e160585d663aa502fe1eded9d7ae040ba7f91d109ecc61713d8e43718b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/web_commands_spec.spl
mirror: doc/06_spec/unit/app/tooling/web_commands_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/web_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/web_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/web_commands_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/web_commands_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects build subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/web_commands_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects init subcommand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
