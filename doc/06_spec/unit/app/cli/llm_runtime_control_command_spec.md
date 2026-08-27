# Llm Runtime Control Command Specification

> Tests covering LLM runtime control CLI command registration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Runtime Control Command Specification

## Scenarios

### LLM runtime control CLI command registration

#### registers llm-runtime-control in command table

- registers llm-runtime-control in command table


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers llm-runtime-control in command table")
val table = source("src/app/cli/dispatch/table.spl")

expect(table).to_contain("name: \"llm-runtime-control\"")
expect(table).to_contain("app_path: \"src/app/llm_runtime/control_cli.spl\"")
```

</details>

#### registers llm-runtime-control in the Rust driver app table

- registers llm-runtime-control in the Rust driver app table


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers llm-runtime-control in the Rust driver app table")
val driver = source("src/compiler_rust/driver/src/main.rs")

expect(driver).to_contain("name: \"llm-runtime-control\"")
expect(driver).to_contain("app_path: \"src/app/llm_runtime/control_cli.spl\"")
expect(driver).to_contain("app_relative_path != \"src/app/llm_runtime/control_cli.spl\"")
expect(driver).to_contain("if app_relative_path == \"src/app/llm_runtime/control_cli.spl\"")
```

</details>

#### keeps direct dispatcher branch routed to runtime owner

- keeps direct dispatcher branch routed to runtime owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps direct dispatcher branch routed to runtime owner")
val dispatcher = source("src/app/cli/_CliMain/main_and_help.spl")

expect(dispatcher).to_contain("elif str_eq(first, \"llm-runtime-control\"):")
expect(dispatcher).to_contain("cli_run_file(\"src/app/llm_runtime/control_cli.spl\", filtered_args")
```

</details>

#### shows operator help for runtime control

- shows operator help for runtime control


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows operator help for runtime control")
val help = source("src/app/cli/cli_helpers.spl")

expect(help).to_contain("simple llm-runtime-control --action preflight")
expect(help).to_contain("--base-model <model> --endpoint <url>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/llm_runtime_control_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM runtime control CLI command registration.
- LLM runtime control CLI command registration

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca76878a1f47b80323d2809ca2b66ca4a0af15309c378a5e37851ad05d4888e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca76878a1f47b80323d2809ca2b66ca4a0af15309c378a5e37851ad05d4888e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca76878a1f47b80323d2809ca2b66ca4a0af15309c378a5e37851ad05d4888e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cli/llm_runtime_control_command_spec.spl
mirror: doc/06_spec/unit/app/cli/llm_runtime_control_command_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/llm_runtime_control_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/llm_runtime_control_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/llm_runtime_control_command_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers llm-runtime-control in command table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/llm_runtime_control_command_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers llm-runtime-control in the Rust driver app table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/llm_runtime_control_command_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps direct dispatcher branch routed to runtime owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
