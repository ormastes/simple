# Formal Delivery Gates Specification

> Tests covering Formal Verification 2.0 staged delivery gates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Formal Delivery Gates Specification

## Scenarios

### Formal Verification 2.0 staged delivery gates

#### accepts an honest partial plan without release readiness

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts an honest partial plan without release readiness
   - Expected: decision.accepted_state is true
   - Expected: decision.release_ready is false
   - Expected: decision.highest_passed_gate equals `aop_macro_closure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts an honest partial plan without release readiness")
val decision = evaluate_formal_delivery_gates_v1(
    ordered_delivery_gates(4), nil)
expect(decision.accepted_state).to_equal(true)
expect(decision.release_ready).to_equal(false)
expect(decision.highest_passed_gate).to_equal("aop_macro_closure")
```

</details>

#### rejects a later pass after an earlier blocker

- rejects a later pass after an earlier blocker
   - Expected: decision.accepted_state is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a later pass after an earlier blocker")
var evidence = ordered_delivery_gates(2)
evidence[4] = passed_gate(FormalDeliveryGateV1.SimpleOsVerticalSlice)
val decision = evaluate_formal_delivery_gates_v1(evidence, nil)
expect(decision.accepted_state).to_equal(false)
expect(decision.diagnostic).to_contain("PREMATURE")
```

</details>

#### requires exact clean evidence for every passed gate

- requires exact clean evidence for every passed gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires exact clean evidence for every passed gate")
var evidence = ordered_delivery_gates(3)
evidence[1] = FormalDeliveryGateEvidenceV1(
    FormalDeliveryGateV1.ExactCoreSemantics,
    FormalDeliveryGateStatusV1.Passed, [], "", "")
val decision = evaluate_formal_delivery_gates_v1(evidence, nil)
expect(decision.diagnostic).to_contain("EVIDENCE")
```

</details>

#### requires the final verified release decision only after all gates

- requires the final verified release decision only after all gates
   - Expected: missing.release_ready is false
   - Expected: ready.accepted_state is true
   - Expected: ready.release_ready is true
   - Expected: ready.highest_passed_gate equals `verified_release`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the final verified release decision only after all gates")
val missing = evaluate_formal_delivery_gates_v1(
    ordered_delivery_gates(8), nil)
expect(missing.release_ready).to_equal(false)
expect(missing.diagnostic).to_contain("RELEASE-DECISION")
val ready = evaluate_formal_delivery_gates_v1(
    ordered_delivery_gates(8), Some(passed_release_bundle()))
expect(ready.accepted_state).to_equal(true)
expect(ready.release_ready).to_equal(true)
expect(ready.highest_passed_gate).to_equal("verified_release")
```

</details>

#### rejects a premature release decision on a partial plan

- rejects a premature release decision on a partial plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a premature release decision on a partial plan")
val decision = evaluate_formal_delivery_gates_v1(
    ordered_delivery_gates(7), Some(passed_release_bundle()))
expect(decision.diagnostic).to_contain("RELEASE-PREMATURE")
```

</details>

#### requires a V2 policy-bound terminal decision for typed verified release

- requires a V2 policy-bound terminal decision for typed verified release
   - Expected: missing.release_ready is false
   - Expected: ready.accepted_state is true
   - Expected: ready.release_ready is true
   - Expected: ready.plan_hash == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a V2 policy-bound terminal decision for typed verified release")
val missing = evaluate_formal_delivery_gates_v2(
    ordered_delivery_gates(8), nil)
expect(missing.release_ready).to_equal(false)
expect(missing.diagnostic).to_contain("RELEASE-DECISION-V2")
val ready = evaluate_formal_delivery_gates_v2(
    ordered_delivery_gates(8), Some(passed_release_bundle_v2()))
expect(ready.accepted_state).to_equal(true)
expect(ready.release_ready).to_equal(true)
expect(ready.plan_hash == "").to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/formal_delivery_gates_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Formal Verification 2.0 staged delivery gates.
- Formal Verification 2.0 staged delivery gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `11d3582c9275d7e01f64bd8a51ffe241ace97e45d83896d892aaf791881e5b56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11d3582c9275d7e01f64bd8a51ffe241ace97e45d83896d892aaf791881e5b56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11d3582c9275d7e01f64bd8a51ffe241ace97e45d83896d892aaf791881e5b56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/assurance/formal_delivery_gates_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/formal_delivery_gates_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/formal_delivery_gates_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/formal_delivery_gates_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/formal_delivery_gates_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts an honest partial plan without release readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_delivery_gates_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a later pass after an earlier blocker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/formal_delivery_gates_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires exact clean evidence for every passed gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
