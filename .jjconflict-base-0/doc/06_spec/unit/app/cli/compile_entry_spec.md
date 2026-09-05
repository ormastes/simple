# Compile Entry Specification

> Tests covering compile_entry normalize_compile_args.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Entry Specification

## Scenarios

### compile_entry normalize_compile_args

#### keeps the compile token and subcommand args after the wrapper paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the compile token and subcommand args after the wrapper paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the compile token and subcommand args after the wrapper paths")
val raw_args = [
    "bin/simple",
    "src/app/cli/compile_entry.spl",
    "compile",
    "src/app/hosted_apps/smux_client.spl",
    "--target",
    "x86_64-unknown-none",
    "-o",
    "/tmp/smux.smf"
]

val args = normalize_compile_args(raw_args)

expect args.len() == 6
expect args[0] == "compile"
expect args[1] == "src/app/hosted_apps/smux_client.spl"
expect args[2] == "--target"
expect args[3] == "x86_64-unknown-none"
expect args[4] == "-o"
expect args[5] == "/tmp/smux.smf"
```

</details>

#### keeps documented run-launcher args after the compile entry sentinel

- keeps documented run-launcher args after the compile entry sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps documented run-launcher args after the compile entry sentinel")
val raw_args = [
    "bin/simple",
    "run",
    "src/app/cli/compile_entry.spl",
    "compile",
    "src/main.spl"
]

val args = normalize_compile_args(raw_args)

expect args.len() == 2
expect args[0] == "compile"
expect args[1] == "src/main.spl"
```

</details>

#### returns an empty list when argv is missing

- returns an empty list when argv is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty list when argv is missing")
val args = normalize_compile_args(nil)
expect args.len() == 0
```

</details>

#### returns an empty list when only wrapper metadata is present

- returns an empty list when only wrapper metadata is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty list when only wrapper metadata is present")
val args = normalize_compile_args(["bin/simple", "src/app/cli/compile_entry.spl"])
expect args.len() == 0
```

</details>

#### returns an empty list when only run-wrapper metadata is present

- returns an empty list when only run-wrapper metadata is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty list when only run-wrapper metadata is present")
val args = normalize_compile_args(["bin/simple", "run", "src/app/cli/compile_entry.spl"])
expect args.len() == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/compile_entry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compile_entry normalize_compile_args.
- compile_entry normalize_compile_args

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `eedd06e075f0f16c9f00f10c4b8bdf3ecd6af36a2bb84c472415fa10b063cb73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eedd06e075f0f16c9f00f10c4b8bdf3ecd6af36a2bb84c472415fa10b063cb73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eedd06e075f0f16c9f00f10c4b8bdf3ecd6af36a2bb84c472415fa10b063cb73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cli/compile_entry_spec.spl
mirror: doc/06_spec/unit/app/cli/compile_entry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/compile_entry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/compile_entry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/compile_entry_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the compile token and subcommand args after the wrapper paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/compile_entry_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps documented run-launcher args after the compile entry sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/compile_entry_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an empty list when argv is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
