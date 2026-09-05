# Before Hook Failure Specification

> Tests covering before hook failure accumulation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Before Hook Failure Specification

## Scenarios

### before hook failure accumulation

#### keeps a hook failure when the body passes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a hook failure when the body passes
   - Expected: "body" equals `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FIXTURES
step("keeps a hook failure when the body passes")
expect("body").to_equal("body")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/fixtures/pure_simple_tooling/before_hook_failure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering before hook failure accumulation.
- before hook failure accumulation

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

- Canonical SPipe generation for source `33403e0071f45004eef731250c7b67f2437510584beba1a7b6ee027861abb4c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33403e0071f45004eef731250c7b67f2437510584beba1a7b6ee027861abb4c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33403e0071f45004eef731250c7b67f2437510584beba1a7b6ee027861abb4c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/fixtures/pure_simple_tooling/before_hook_failure_spec.spl
mirror: doc/06_spec/fixtures/pure_simple_tooling/before_hook_failure_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/fixtures/pure_simple_tooling/before_hook_failure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/fixtures/pure_simple_tooling/before_hook_failure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/fixtures/pure_simple_tooling/before_hook_failure_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/fixtures/pure_simple_tooling/before_hook_failure_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a hook failure when the body passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
