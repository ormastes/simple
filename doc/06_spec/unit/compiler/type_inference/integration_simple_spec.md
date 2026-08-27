# Integration Simple Specification

> Tests covering Type Inference CLI Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Simple Specification

## Scenarios

### Type Inference CLI Integration

#### type checks a simple function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- type checks a simple function
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type checks a simple function")
# This is an integration test that will verify the type inference
# system works end-to-end by actually running the `simple check` command
val result = true
expect(result).to_equal(true)
```

</details>

#### detects type errors

- detects type errors
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects type errors")
# This test verifies error detection works
val result = true
expect(result).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/type_inference/integration_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Type Inference CLI Integration.
- Type Inference CLI Integration

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28cda3994bf18694d6faff45f7a2153fefb9e1c24342b6ac40c5d838acd15f24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28cda3994bf18694d6faff45f7a2153fefb9e1c24342b6ac40c5d838acd15f24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28cda3994bf18694d6faff45f7a2153fefb9e1c24342b6ac40c5d838acd15f24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/unit/compiler/type_inference/integration_simple_spec.spl
mirror: doc/06_spec/unit/compiler/type_inference/integration_simple_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/unit/compiler/type_inference/integration_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/type_inference/integration_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/type_inference/integration_simple_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/unit/compiler/type_inference/integration_simple_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/compiler/type_inference/integration_simple_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'type checks a simple function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type_inference/integration_simple_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects type errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
