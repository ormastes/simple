# Rv32i Delivery Gate Specification

> Tests covering FV2 generated RV32I end-to-end gate collector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32i Delivery Gate Specification

## Scenarios

### FV2 generated RV32I end-to-end gate collector

#### fails closed without runner-owned RV32 execution authority

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed without runner-owned RV32 execution authority
   - Expected: collection.gate_evidence.status.name() equals `failed`
   - Expected: collection.gate_evidence.receipt_hashes.len() equals `0`
   - Expected: collection.receipt_files.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed without runner-owned RV32 execution authority")
val collection = collect_generated_rv32i_end_to_end_gate_v1(
    rv32_formal(), rv32_equivalence(), rv32_sail(),
    rv32_hwir_to_rtl(), rv32_materials())
expect(collection.gate_evidence.status.name()).to_equal("failed")
expect(collection.gate_evidence.diagnostic).to_contain(
    "RV32I-EXECUTION-AUTHORITY")
expect(collection.gate_evidence.receipt_hashes.len()).to_equal(0)
expect(collection.receipt_files.len()).to_equal(0)
```

</details>

#### rejects missing material identity drift and incomplete formal scope

- rejects missing material identity drift and incomplete formal scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects missing material identity drift and incomplete formal scope")
var missing = rv32_materials()
missing.pop()
expect(collect_generated_rv32i_end_to_end_gate_v1(
    rv32_formal(), rv32_equivalence(), rv32_sail(),
    rv32_hwir_to_rtl(), missing).gate_evidence.diagnostic).to_contain(
        "MATERIAL-COUNT")
var drift = rv32_sail()
drift.rtl_hash = sha256_text("other-rtl")
expect(collect_generated_rv32i_end_to_end_gate_v1(
    rv32_formal(), rv32_equivalence(), drift,
    rv32_hwir_to_rtl(), rv32_materials()).gate_evidence.diagnostic).to_contain("BINDING")
var weak = rv32_formal()
weak.property_ids = ["rv32i.add.result"]
expect(collect_generated_rv32i_end_to_end_gate_v1(
    weak, rv32_equivalence(), rv32_sail(),
    rv32_hwir_to_rtl(), rv32_materials()).gate_evidence.diagnostic).to_contain("FORMAL-SCOPE")
var wrong_edge = rv32_hwir_to_rtl()
wrong_edge.after_semantic_hash = sha256_text("other-rtl")
wrong_edge.certificate_hash = wrong_edge.expected_certificate_hash()
expect(collect_generated_rv32i_end_to_end_gate_v1(
    rv32_formal(), rv32_equivalence(), rv32_sail(), wrong_edge,
    rv32_materials()).gate_evidence.diagnostic).to_contain("HWIR-RTL")
```

</details>

#### does not confuse protocol-specified jobs with executed model evidence

- does not confuse protocol-specified jobs with executed model evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not confuse protocol-specified jobs with executed model evidence")
var specified = rv32_formal()
specified.status = FormalStatus.Specified
expect(collect_generated_rv32i_end_to_end_gate_v1(
    specified, rv32_equivalence(), rv32_sail(),
    rv32_hwir_to_rtl(), rv32_materials()).gate_evidence.diagnostic).to_contain("STATUS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/rv32i_delivery_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 generated RV32I end-to-end gate collector.
- FV2 generated RV32I end-to-end gate collector

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `173433f7cd0570b71ea84fbf97af56d4b7b7f39a7ed7ec0991292eb43be96167`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `173433f7cd0570b71ea84fbf97af56d4b7b7f39a7ed7ec0991292eb43be96167`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `173433f7cd0570b71ea84fbf97af56d4b7b7f39a7ed7ec0991292eb43be96167`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/verification/rv32i_delivery_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/rv32i_delivery_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/rv32i_delivery_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/rv32i_delivery_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/rv32i_delivery_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/verification/rv32i_delivery_gate_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed without runner-owned RV32 execution authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/rv32i_delivery_gate_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing material identity drift and incomplete formal scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/rv32i_delivery_gate_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not confuse protocol-specified jobs with executed model evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
