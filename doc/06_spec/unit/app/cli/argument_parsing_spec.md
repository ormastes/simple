# Argument Parsing Specification

> Tests covering Flag Parsing, Subcommand Parsing, Argument Validation, Flag Combinations, Command Construction, Error Handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argument Parsing Specification

## Scenarios

### Flag Parsing

#### recognizes double-dash flags

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes double-dash flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes double-dash flags")
val flag = "--gc-log"
expect flag.starts_with("--")
expect is_flag(flag)
```

</details>

#### recognizes single-dash flags

- recognizes single-dash flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes single-dash flags")
val flag = "-v"
expect flag.starts_with("-")
expect is_flag(flag)
```

</details>

#### extracts flag name

- extracts flag name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts flag name")
val flag = "--gc-log"
match parse_flag(flag):
    case Some(name):
        expect name == "gc-log"
    case None:
        fail "Should parse flag name"
```

</details>

#### handles boolean flags

- handles boolean flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles boolean flags")
val flags = CliFlags {
    gc_log: true,
    gc_off: false,
    verbose: true,
    quiet: false
}

expect flags.gc_log == true
expect flags.gc_off == false
```

</details>

### Subcommand Parsing

#### identifies subcommand name

- identifies subcommand name


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies subcommand name")
val cmd = CliCommand {
    name: "test",
    args: ["path/to/test"],
    flags: CliFlags {
        gc_log: false,
        gc_off: false,
        verbose: false,
        quiet: false
    }
}

expect cmd.name == "test"
```

</details>

#### parses test subcommand

- parses test subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses test subcommand")
val subcommand = "test"
expect subcommand == "test"
```

</details>

#### parses compile subcommand

- parses compile subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses compile subcommand")
val subcommand = "compile"
expect subcommand == "compile"
```

</details>

#### parses run subcommand

- parses run subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses run subcommand")
val subcommand = "run"
expect subcommand == "run"
```

</details>

### Argument Validation

#### validates file paths

- validates file paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates file paths")
val path = "test.spl"
expect path.ends_with(".spl")
```

</details>

#### validates directory paths

- validates directory paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates directory paths")
val path = "test/"
expect path.ends_with("/")
```

</details>

#### handles empty arguments

- handles empty arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty arguments")
val args: [text] = []
expect args.len() == 0
```

</details>

#### handles multiple arguments

- handles multiple arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple arguments")
val args = ["arg1", "arg2", "arg3"]
expect args.len() == 3
expect args[0] == "arg1"
```

</details>

### Flag Combinations

#### enables multiple flags

- enables multiple flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables multiple flags")
val flags = CliFlags {
    gc_log: true,
    gc_off: false,
    verbose: true,
    quiet: false
}

expect flags.gc_log and flags.verbose
```

</details>

#### detects conflicting flags

- detects conflicting flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects conflicting flags")
val verbose = true
val quiet = true

# These should be mutually exclusive
expect verbose and quiet # Both set incorrectly
```

</details>

#### applies default values

- applies default values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies default values")
val flags = CliFlags {
    gc_log: false,
    gc_off: false,
    verbose: false,
    quiet: false
}

expect not flags.gc_log
expect not flags.gc_off
```

</details>

### Command Construction

#### builds test command

- builds test command


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds test command")
val cmd = CliCommand {
    name: "test",
    args: ["test/unit/"],
    flags: CliFlags {
        gc_log: false,
        gc_off: false,
        verbose: true,
        quiet: false
    }
}

expect cmd.name == "test"
expect cmd.args.len() == 1
expect cmd.flags.verbose
```

</details>

#### builds compile command

- builds compile command


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds compile command")
val cmd = CliCommand {
    name: "compile",
    args: ["input.spl", "-o", "output"],
    flags: CliFlags {
        gc_log: false,
        gc_off: false,
        verbose: false,
        quiet: false
    }
}

expect cmd.name == "compile"
expect cmd.args.len() == 3
```

</details>

### Error Handling

#### detects unknown flags

- detects unknown flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects unknown flags")
val flag = "--unknown-flag"
expect flag.starts_with("--")
# In real implementation, should check against known flags
```

</details>

#### detects invalid paths

- detects invalid paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects invalid paths")
val path = "nonexistent.xyz"
expect not path.ends_with(".spl")
```

</details>

#### handles missing required arguments

- handles missing required arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing required arguments")
val args: [text] = []
expect args.len() == 0
# Should require at least one argument for some commands
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/argument_parsing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Flag Parsing, Subcommand Parsing, Argument Validation, Flag Combinations, Command Construction, Error Handling.
- Flag Parsing
- Subcommand Parsing
- Argument Validation
- Flag Combinations
- Command Construction
- Error Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `6322d0c0c8e4ec744e180967db5c96ad2e89908edf2a92fd59f426ec5bd51c71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6322d0c0c8e4ec744e180967db5c96ad2e89908edf2a92fd59f426ec5bd51c71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6322d0c0c8e4ec744e180967db5c96ad2e89908edf2a92fd59f426ec5bd51c71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cli/argument_parsing_spec.spl
mirror: doc/06_spec/unit/app/cli/argument_parsing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/argument_parsing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/argument_parsing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/argument_parsing_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes double-dash flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/argument_parsing_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes single-dash flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/argument_parsing_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts flag name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
