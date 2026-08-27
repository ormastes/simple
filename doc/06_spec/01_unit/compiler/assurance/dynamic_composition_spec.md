# Dynamic Composition Specification

> Tests covering FV2 dynamic verified composition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Composition Specification

## Scenarios

### FV2 dynamic verified composition

#### admits only a fully matching signed verified component

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits only a fully matching signed verified component
   - Expected: decision.admitted is true
   - Expected: decision.closed_verification is true
   - Expected: decision.status equals `FormalStatus.ArtifactVerified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits only a fully matching signed verified component")
val component = plugin_receipt()
val decision = verify_dynamic_composition_v1(composition_policy(), component, verified_signature(component), [closed_obligation()])
expect(decision.admitted).to_equal(true)
expect(decision.closed_verification).to_equal(true)
expect(decision.status).to_equal(FormalStatus.ArtifactVerified)
```

</details>

#### rejects interface lineage signer and profile mismatches

- rejects interface lineage signer and profile mismatches
   - Expected: decision.admitted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects interface lineage signer and profile mismatches")
val component = plugin_receipt()
val bad_policy = DynamicCompositionPolicyV1("different-api", "verified", "compiler-lineage", ["other-key"])
val decision = verify_dynamic_composition_v1(bad_policy, component, verified_signature(component), [closed_obligation()])
expect(decision.admitted).to_equal(false)
expect(decision.diagnostic).to_contain("SIGNER-POLICY")
```

</details>

#### rejects a signature over a stale component receipt

- rejects a signature over a stale component receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a signature over a stale component receipt")
val component = plugin_receipt()
val stale = SignatureVerificationReceiptV1("stale-hash", component.signer_id, "ed25519-checker-v1", "signature-evidence", true)
val decision = verify_dynamic_composition_v1(composition_policy(), component, stale, [closed_obligation()])
expect(decision.diagnostic).to_contain("SIGNATURE-BINDING")
```

</details>

#### rejects an absent or undischarged composition obligation

- rejects an absent or undischarged composition obligation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an absent or undischarged composition obligation")
val component = plugin_receipt()
val missing = verify_dynamic_composition_v1(composition_policy(), component, verified_signature(component), [])
expect(missing.diagnostic).to_contain("OBLIGATION-MISSING")
val open = CompositionObligationV1("interface-refinement", "proposition", "certificate", false)
val undischarged = verify_dynamic_composition_v1(composition_policy(), component, verified_signature(component), [open])
expect(undischarged.diagnostic).to_contain("OBLIGATION")
```

</details>

#### labels an explicitly isolated component as bounded TCB rather than closed

- labels an explicitly isolated component as bounded TCB rather than closed
   - Expected: decision.admitted is true
   - Expected: decision.closed_verification is false
   - Expected: decision.status equals `FormalStatus.TrustedBoundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("labels an explicitly isolated component as bounded TCB rather than closed")
val decision = declare_dynamic_bounded_tcb_v1(plugin_receipt(), "trust-manifest")
expect(decision.admitted).to_equal(true)
expect(decision.closed_verification).to_equal(false)
expect(decision.status).to_equal(FormalStatus.TrustedBoundary)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/assurance/dynamic_composition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 dynamic verified composition.
- FV2 dynamic verified composition

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

- Canonical SPipe generation for source `b0ad958a27713aa950485faa24153d93ec3b1537730d9f7b8f3fb2421cefb5e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b0ad958a27713aa950485faa24153d93ec3b1537730d9f7b8f3fb2421cefb5e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b0ad958a27713aa950485faa24153d93ec3b1537730d9f7b8f3fb2421cefb5e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/assurance/dynamic_composition_spec.spl
mirror: doc/06_spec/01_unit/compiler/assurance/dynamic_composition_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/assurance/dynamic_composition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/assurance/dynamic_composition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/assurance/dynamic_composition_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only a fully matching signed verified component' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/dynamic_composition_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects interface lineage signer and profile mismatches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/assurance/dynamic_composition_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a signature over a stale component receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
