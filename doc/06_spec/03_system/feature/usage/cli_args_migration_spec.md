# CLI Args Migration Compatibility Specification

> Tests compatibility between the new cli keyword and the existing manual argument parsing pattern. Projects using manual arg parsing should be able to incrementally migrate to the cli keyword without breaking existing functionality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Migration Compatibility Specification

Tests compatibility between the new cli keyword and the existing manual argument parsing pattern. Projects using manual arg parsing should be able to incrementally migrate to the cli keyword without breaking existing functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-011 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_migration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compatibility between the new cli keyword and the existing manual
argument parsing pattern. Projects using manual arg parsing should be
able to incrementally migrate to the cli keyword without breaking
existing functionality.

## Manual Pattern (Before)

```simple
use std.spec.step

val args = get_args()
var verbose = false
var output = "default.txt"
for arg in args:
    if arg == "--verbose":
        verbose = true
    elif arg == "--output":
        output = next_arg()
```

## CLI Keyword (After)

```simple
cli:
    verbose: false
    output: "default.txt"
```

## Scenarios

### CLI Args Migration Compatibility

#### equivalent behavior

#### produces same defaults as manual parsing

- produces same defaults as manual parsing
   - Expected: cli_verbose equals `manual_verbose`
   - Expected: cli_output equals `manual_output`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces same defaults as manual parsing")
# Manual pattern:
# var verbose = false
# var output = "default.txt"
#
# CLI keyword:
# cli:
#     verbose: false
#     output: "default.txt"
#
# Both should yield the same default values
val manual_verbose = false
val manual_output = "default.txt"
val cli_verbose = false
val cli_output = "default.txt"
expect(cli_verbose).to_equal(manual_verbose)
expect(cli_output).to_equal(manual_output)
```

</details>

#### produces same parsed values as manual parsing

- produces same parsed values as manual parsing
   - Expected: cli_verbose equals `manual_verbose`
   - Expected: cli_output equals `manual_output`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces same parsed values as manual parsing")
# Given args: ["--verbose", "--output", "custom.txt"]
# Manual: loops and matches each arg
# CLI: cli.parse(args) returns struct
# Both should produce verbose=true, output="custom.txt"
val manual_verbose = true
val manual_output = "custom.txt"
val cli_verbose = true
val cli_output = "custom.txt"
expect(cli_verbose).to_equal(manual_verbose)
expect(cli_output).to_equal(manual_output)
```

</details>

#### incremental migration

#### can coexist with manual parsing in same project

- can coexist with manual parsing in same project
   - Expected: cli_module_works is true
   - Expected: manual_module_works is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can coexist with manual parsing in same project")
# Some modules use cli keyword, others use manual parsing
# No conflicts between the two approaches
val cli_module_works = true
val manual_module_works = true
expect(cli_module_works).to_equal(true)
expect(manual_module_works).to_equal(true)
```

</details>

#### supports gradual option-by-option migration

- supports gradual option-by-option migration
   - Expected: partial_migration is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports gradual option-by-option migration")
# A project can migrate one option at a time from manual to cli
# The cli keyword does not require all-or-nothing adoption
val partial_migration = true
expect(partial_migration).to_equal(true)
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

- Canonical SPipe generation for source `771ac823b07bee5952e3feae8d0cfe554aa448c4599d73cfb0e529879919bf03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `771ac823b07bee5952e3feae8d0cfe554aa448c4599d73cfb0e529879919bf03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `771ac823b07bee5952e3feae8d0cfe554aa448c4599d73cfb0e529879919bf03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/usage/cli_args_migration_spec.spl
mirror: doc/06_spec/03_system/feature/usage/cli_args_migration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/cli_args_migration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/cli_args_migration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/cli_args_migration_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces same defaults as manual parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_migration_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces same parsed values as manual parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/cli_args_migration_spec.spl:92:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can coexist with manual parsing in same project' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/usage/cli_args_migration_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can coexist with manual parsing in same project' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
