# Rv64 Delivery Gate Specification

> Tests covering FV2 RV64 privilege MMU and Linux delivery gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Delivery Gate Specification

## Scenarios

### FV2 RV64 privilege MMU and Linux delivery gate

#### keeps formal refinement and executed validation evidence distinct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps formal refinement and executed validation evidence distinct
   - Expected: collection.gate_evidence.status.name() equals `passed`
   - Expected: collection.gate_evidence.receipt_hashes.len() equals `21`
   - Expected: collection.receipt_files.len() equals `21`
   - Expected: sha256_text(file.content) equals `file.receipt_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps formal refinement and executed validation evidence distinct")
val collection = collect_rv64_privilege_mmu_linux_gate_v1(
    rv64_identity(), rv64_checks(), rv64_proof_material())
expect(collection.gate_evidence.status.name()).to_equal("passed")
expect(collection.gate_evidence.receipt_hashes.len()).to_equal(21)
expect(collection.receipt_files.len()).to_equal(21)
for file in collection.receipt_files:
    expect(sha256_text(file.content)).to_equal(file.receipt_hash)
```

</details>

#### rejects reorder product drift missing proof and validation impersonation

- rejects reorder product drift missing proof and validation impersonation


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects reorder product drift missing proof and validation impersonation")
var reordered = rv64_checks()
val temporary = reordered[0]
reordered[0] = reordered[1]
reordered[1] = temporary
expect(collect_rv64_privilege_mmu_linux_gate_v1(rv64_identity(),
    reordered, rv64_proof_material()).gate_evidence.diagnostic).to_contain(
        "ORDER")
var drift = rv64_checks()
drift[2].product_identity_hash = sha256_text("other-product")
expect(collect_rv64_privilege_mmu_linux_gate_v1(rv64_identity(), drift,
    rv64_proof_material()).gate_evidence.diagnostic).to_contain("BINDING")
var missing = rv64_proof_material()
missing.pop()
expect(collect_rv64_privilege_mmu_linux_gate_v1(rv64_identity(),
    rv64_checks(), missing).gate_evidence.diagnostic).to_contain(
        "PROOF-COUNT")
var impersonated = rv64_checks()
impersonated[5].proof_or_certificate_hash = sha256_text("fake-proof")
expect(collect_rv64_privilege_mmu_linux_gate_v1(rv64_identity(),
    impersonated, rv64_proof_material()).gate_evidence.diagnostic).to_contain(
        "VALIDATION-CLASS")
```

</details>

#### rejects timeout and output substitution

- rejects timeout and output substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects timeout and output substitution")
var timed_out = rv64_checks()
timed_out[6].outcome = ExecutedCheckOutcomeV1.Timeout
expect(collect_rv64_privilege_mmu_linux_gate_v1(rv64_identity(),
    timed_out, rv64_proof_material()).gate_evidence.status.name()).to_equal(
        "failed")
var duplicate_output = rv64_checks()
duplicate_output[6].retained_output = duplicate_output[5].retained_output
expect(collect_rv64_privilege_mmu_linux_gate_v1(rv64_identity(),
    duplicate_output, rv64_proof_material()).gate_evidence.diagnostic).to_contain(
        "OUTPUT-DUPLICATE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verification/rv64_delivery_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FV2 RV64 privilege MMU and Linux delivery gate.
- FV2 RV64 privilege MMU and Linux delivery gate

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

- Canonical SPipe generation for source `5dcfc21f2964e6f17c73e63b0eabf6534d0f57cb4363f67f7b5f50a90f74005b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5dcfc21f2964e6f17c73e63b0eabf6534d0f57cb4363f67f7b5f50a90f74005b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5dcfc21f2964e6f17c73e63b0eabf6534d0f57cb4363f67f7b5f50a90f74005b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/verification/rv64_delivery_gate_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/rv64_delivery_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/rv64_delivery_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/rv64_delivery_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/rv64_delivery_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/verification/rv64_delivery_gate_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps formal refinement and executed validation evidence distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/rv64_delivery_gate_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects reorder product drift missing proof and validation impersonation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/rv64_delivery_gate_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects timeout and output substitution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
