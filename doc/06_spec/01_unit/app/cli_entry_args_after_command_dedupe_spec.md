# Cli Entry Args After Command Dedupe Specification

> Tests covering CLI entry args_after_command dedupe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Entry Args After Command Dedupe Specification

## Scenarios

### CLI entry args_after_command dedupe

#### defines the shared args_after_named_command helper in cli_util

- defines the shared args_after_named_command helper in cli_util


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines the shared args_after_named_command helper in cli_util")
val source = rt_file_read_text("src/app/cli_util.spl") ?? ""

expect(source).to_contain("fn args_after_named_command(raw: [text], entry_suffix: text, command_name: text) -> [text]")
expect(source).to_contain("export args_after_named_command")
```

</details>

#### routes vscode_entry through the shared helper instead of a hand-rolled scan

- routes vscode_entry through the shared helper instead of a hand-rolled scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes vscode_entry through the shared helper instead of a hand-rolled scan")
val source = cli_source("vscode_entry.spl")

expect(source).to_contain("use app.cli_util.\{args_after_named_command\}")
expect(source).to_contain("args_after_named_command(get_cli_args(), \"vscode_entry.spl\", \"vscode\")")
```

</details>

#### routes electron_entry through the shared helper instead of a hand-rolled scan

- routes electron_entry through the shared helper instead of a hand-rolled scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes electron_entry through the shared helper instead of a hand-rolled scan")
val source = cli_source("electron_entry.spl")

expect(source).to_contain("use app.cli_util.\{args_after_named_command\}")
expect(source).to_contain("args_after_named_command(get_cli_args(), \"electron_entry.spl\", \"electron\")")
```

</details>

#### routes security_entry through the shared helper instead of a hand-rolled scan

- routes security_entry through the shared helper instead of a hand-rolled scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes security_entry through the shared helper instead of a hand-rolled scan")
val source = cli_source("security_entry.spl")

expect(source).to_contain("use app.cli_util.\{args_after_named_command\}")
expect(source).to_contain("args_after_named_command(get_cli_args(), \"security_entry.spl\", \"security\")")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli_entry_args_after_command_dedupe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI entry args_after_command dedupe.
- CLI entry args_after_command dedupe

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

- Canonical SPipe generation for source `8549d3b98aa9a7014ea538faabd10ea1e95d574cdcb1fbed8d4fba03f592d8e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8549d3b98aa9a7014ea538faabd10ea1e95d574cdcb1fbed8d4fba03f592d8e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8549d3b98aa9a7014ea538faabd10ea1e95d574cdcb1fbed8d4fba03f592d8e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli_entry_args_after_command_dedupe_spec.spl
mirror: doc/06_spec/01_unit/app/cli_entry_args_after_command_dedupe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli_entry_args_after_command_dedupe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli_entry_args_after_command_dedupe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli_entry_args_after_command_dedupe_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines the shared args_after_named_command helper in cli_util' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli_entry_args_after_command_dedupe_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes vscode_entry through the shared helper instead of a hand-rolled scan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli_entry_args_after_command_dedupe_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes electron_entry through the shared helper instead of a hand-rolled scan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
