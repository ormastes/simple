# CLI Args Error Handling Specification

> Tests compile-time and runtime error cases for the cli keyword. The compiler should catch invalid cli blocks at compile time, and the runtime should produce clear error messages for bad input.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Error Handling Specification

Tests compile-time and runtime error cases for the cli keyword. The compiler should catch invalid cli blocks at compile time, and the runtime should produce clear error messages for bad input.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-009 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_error_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compile-time and runtime error cases for the cli keyword.
The compiler should catch invalid cli blocks at compile time,
and the runtime should produce clear error messages for bad input.

## Key Error Cases

- Duplicate option names
- Invalid default value types
- Unknown options at runtime
- Missing required positional args
- Type mismatch at runtime (e.g., "abc" for int option)
- Duplicate subcommand names
- Reserved option names (--help, --version)

## Scenarios

### CLI Args Error Handling

#### compile-time errors

#### rejects duplicate option names

- rejects duplicate option names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects duplicate option names")
# cli:
#     verbose: false
#     verbose: true    # ERROR: duplicate option 'verbose'
val error = "duplicate option 'verbose'"
expect(error).to_contain("duplicate")
```

</details>

#### rejects invalid default expression

- rejects invalid default expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid default expression")
# cli:
#     count: some_function()  # ERROR: default must be literal
val error = "default must be a literal value"
expect(error).to_contain("literal")
```

</details>

#### rejects duplicate subcommand names

- rejects duplicate subcommand names


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects duplicate subcommand names")
# cli:
#     command build:
#         target: "debug"
#     command build:           # ERROR: duplicate subcommand 'build'
#         mode: "fast"
val error = "duplicate subcommand 'build'"
expect(error).to_contain("duplicate subcommand")
```

</details>

#### warns on reserved option names

- warns on reserved option names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns on reserved option names")
# cli:
#     help: false    # WARNING: 'help' is reserved for --help
val warning = "option 'help' conflicts with built-in --help"
expect(warning).to_contain("conflicts with built-in")
0
```

</details>

#### runtime errors

#### reports unknown option

- reports unknown option


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports unknown option")
# cli:
#     verbose: false
# cli.parse(["--unknown"]) should error
val error = "unknown option '--unknown'"
expect(error).to_start_with("unknown option")
```

</details>

#### reports missing value for option

- reports missing value for option


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports missing value for option")
# cli:
#     output: "default.txt"
# cli.parse(["--output"]) without value should error
val error = "option '--output' requires a value"
expect(error).to_contain("requires a value")
```

</details>

#### reports type mismatch

- reports type mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports type mismatch")
# cli:
#     count: 1
# cli.parse(["--count", "abc"]) should error
val error = "invalid value 'abc' for option '--count': expected integer"
expect(error).to_contain("invalid value")
expect(error).to_contain("expected integer")
```

</details>

#### reports missing required positional

- reports missing required positional


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports missing required positional")
# cli:
#     command run:
#         positional file: text
# cli.parse(["run"]) without file should error
val error = "missing required argument: file"
expect(error).to_contain("missing required")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `962734d8effcf6b750adbc784d30d34e51f3788a3deec0b65fc3e20b56cd3798`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `962734d8effcf6b750adbc784d30d34e51f3788a3deec0b65fc3e20b56cd3798`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `962734d8effcf6b750adbc784d30d34e51f3788a3deec0b65fc3e20b56cd3798`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/cli_args_error_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_error_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cli_args_error_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_error_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_error_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate option names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_error_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid default expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_error_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate subcommand names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
