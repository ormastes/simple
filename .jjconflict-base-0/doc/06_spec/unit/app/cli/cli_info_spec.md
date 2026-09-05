# Cli Info Specification

> Tests covering CLI Info Commands.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Info Specification

## Scenarios

### CLI Info Commands

#### targets app

#### has Simple app wrapper

- has Simple app wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Simple app wrapper")
expect rt_file_exists_str("src/app/targets/main.spl")
```

</details>

#### linkers app

#### has Simple app wrapper

- has Simple app wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Simple app wrapper")
expect rt_file_exists_str("src/app/linkers/main.spl")
```

</details>

#### info app

#### has Simple app wrapper

- has Simple app wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Simple app wrapper")
expect rt_file_exists_str("src/app/info/main.spl")
```

</details>

#### env app

#### has Simple app wrapper

- has Simple app wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Simple app wrapper")
expect rt_file_exists_str("src/app/env/main.spl")
```

</details>

#### brief app

#### has Simple app wrapper

- has Simple app wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Simple app wrapper")
expect rt_file_exists_str("src/app/brief/main.spl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/cli_info_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI Info Commands.
- CLI Info Commands

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

- Canonical SPipe generation for source `0f8862840f60b0630fa7d6a9ffdf6c68c57e77eeed2fcd6bc93a5d0db108818b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f8862840f60b0630fa7d6a9ffdf6c68c57e77eeed2fcd6bc93a5d0db108818b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f8862840f60b0630fa7d6a9ffdf6c68c57e77eeed2fcd6bc93a5d0db108818b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/cli/cli_info_spec.spl
mirror: doc/06_spec/unit/app/cli/cli_info_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/cli_info_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/cli_info_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/cli_info_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Simple app wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/cli_info_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Simple app wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/cli_info_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Simple app wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
