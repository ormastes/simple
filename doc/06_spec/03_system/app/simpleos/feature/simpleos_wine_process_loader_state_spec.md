# Simpleos Wine Process Loader State Specification

> Tests covering SimpleOS Wine process import loader state, REQ-038: modeled import loader state with refcount release and rollback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Loader State Specification

## Scenarios

### SimpleOS Wine process import loader state

### REQ-038: modeled import loader state with refcount release and rollback

#### should own modeled multi-DLL loader state without real DLL loading or PE execution

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine process import loader state, REQ-038: modeled import loader state with refcount release and rollback.
- SimpleOS Wine process import loader state
- REQ-038: modeled import loader state with refcount release and rollback

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

- `REQ-SSPEC-SYSTEM`
- `REQ-038`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fbb361a5613974ae00dd05f724f955b2661fc12e1cc213ba253df3c2a541358d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fbb361a5613974ae00dd05f724f955b2661fc12e1cc213ba253df3c2a541358d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fbb361a5613974ae00dd05f724f955b2661fc12e1cc213ba253df3c2a541358d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=85 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl:64:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should own modeled multi-DLL loader state without real DLL loading or PE execution' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/simpleos/feature/simpleos_wine_process_loader_state_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should own modeled multi-DLL loader state without real DLL loading or PE execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
