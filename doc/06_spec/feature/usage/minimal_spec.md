# Minimal Test Spec

> A minimal smoke test that verifies the test runner can load a spec file with a basic describe/it block and execute a trivial assertion. Used as a baseline sanity check for the SPipe framework and test infrastructure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Minimal Test Spec

A minimal smoke test that verifies the test runner can load a spec file with a basic describe/it block and execute a trivial assertion. Used as a baseline sanity check for the SPipe framework and test infrastructure.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEST-002 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/feature/usage/minimal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A minimal smoke test that verifies the test runner can load a spec file
with a basic describe/it block and execute a trivial assertion. Used as a
baseline sanity check for the SPipe framework and test infrastructure.

## Syntax

```simple
use std.spec.step

describe "Test":
    # @manual scenario evidence
it "works":
    # @req REQ-SSPEC-FEATURE
    step("works")
check(true)
```

## Scenarios

### Test

#### works

- works


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works")
check(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `51f7bb7890c730b3de6dbf80adc70a1ad540dee866edfaf75eff1c0b9328d2ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51f7bb7890c730b3de6dbf80adc70a1ad540dee866edfaf75eff1c0b9328d2ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51f7bb7890c730b3de6dbf80adc70a1ad540dee866edfaf75eff1c0b9328d2ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/feature/usage/minimal_spec.spl
mirror: doc/06_spec/feature/usage/minimal_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=95 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/feature/usage/minimal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/minimal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/minimal_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/feature/usage/minimal_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'works' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/minimal_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
