# Phase4 Cli Smoke Specification

> Tests covering Phase 4 full CLI test dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Phase4 Cli Smoke Specification

## Scenarios

### Phase 4 full CLI test dispatch

#### should execute a real assertion through the full test runner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should execute a real assertion through the full test runner
   - Expected: "phase4-caret-cli" equals `phase4-caret-cli`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FIXTURES
step("should execute a real assertion through the full test runner")
expect("phase4-caret-cli").to_equal("phase4-caret-cli")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Phase 4 full CLI test dispatch.
- Phase 4 full CLI test dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FIXTURES`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d17af5e86feea7ad6c967fcced6222e7c98bdb6e16730ba90fef12b70b3f0cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d17af5e86feea7ad6c967fcced6222e7c98bdb6e16730ba90fef12b70b3f0cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d17af5e86feea7ad6c967fcced6222e7c98bdb6e16730ba90fef12b70b3f0cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.spl
mirror: doc/06_spec/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.spl:11:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute a real assertion through the full test runner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/fixtures/app/llm_caret/messaging/phase4_cli_smoke_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should execute a real assertion through the full test runner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
