# CLI Args mod.spl Embedding Specification

> Tests embedding the cli keyword in mod.spl module files. When a module's mod.spl contains a cli block, the module becomes an executable entry point that can be run directly. This enables self-contained CLI tools as modules.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args mod.spl Embedding Specification

Tests embedding the cli keyword in mod.spl module files. When a module's mod.spl contains a cli block, the module becomes an executable entry point that can be run directly. This enables self-contained CLI tools as modules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-010 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_modspl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests embedding the cli keyword in mod.spl module files. When a module's
mod.spl contains a cli block, the module becomes an executable entry point
that can be run directly. This enables self-contained CLI tools as modules.

## Syntax

```simple
# src/app/my_tool/mod.spl
cli:
    verbose: false
    output: "result.txt"

use std.spec.step

fn main(args: CliArgs):
    if args.verbose:
        print "Verbose mode enabled"
    process(args.output)
```

## Scenarios

### CLI Args mod.spl Embedding

#### module entry point

#### defines cli in mod.spl

- defines cli in mod.spl
   - Expected: is_entry_point is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines cli in mod.spl")
# A mod.spl file with a cli block should be treated as
# an executable module entry point
val is_entry_point = true
expect(is_entry_point).to_equal(true)
```

</details>

#### generates CliArgs struct in module scope

- generates CliArgs struct in module scope
   - Expected: struct_name equals `CliArgs`
   - Expected: scope equals `module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates CliArgs struct in module scope")
# The generated struct should be accessible within the module
val struct_name = "CliArgs"
val scope = "module"
expect(struct_name).to_equal("CliArgs")
expect(scope).to_equal("module")
```

</details>

#### module interaction

#### allows importing module functions alongside cli

- allows importing module functions alongside cli
   - Expected: can_import is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows importing module functions alongside cli")
# Other modules can import functions from a module that has cli
# use my_tool.{process, format_output}
val can_import = true
expect(can_import).to_equal(true)
```

</details>

#### does not export CliArgs struct by default

- does not export CliArgs struct by default
   - Expected: is_exported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not export CliArgs struct by default")
# The generated CliArgs struct is private to the module
# External modules should not see it
val is_exported = false
expect(is_exported).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `7aa883925e29c4cb8f97ee4b643b5d8069603aba369e34c62409eabd0b6c16bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7aa883925e29c4cb8f97ee4b643b5d8069603aba369e34c62409eabd0b6c16bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7aa883925e29c4cb8f97ee4b643b5d8069603aba369e34c62409eabd0b6c16bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **72/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/cli_args_modspl_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_modspl_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=72; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/cli_args_modspl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_modspl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_modspl_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/usage/cli_args_modspl_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/feature/usage/cli_args_modspl_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines cli in mod.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_modspl_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates CliArgs struct in module scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_modspl_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows importing module functions alongside cli' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
