# X25519mlkem768 Gpu Final Evidence Specification

> Tests covering X25519MLKEM768 typed GPU final evidence selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Final Evidence Specification

## Scenarios

### X25519MLKEM768 typed GPU final evidence selection

#### admits only CUDA and Vulkan into the same-run typed observation path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits only CUDA and Vulkan into the same-run typed observation path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("admits only CUDA and Vulkan into the same-run typed observation path")
expect(x25519_mlkem768_gpu_final_evidence_backend_reason(
    X25519MlKem768EvidenceBackend.Cuda)).to_equal("")
expect(x25519_mlkem768_gpu_final_evidence_backend_reason(
    X25519MlKem768EvidenceBackend.Vulkan)).to_equal("")
```

</details>

#### rejects Metal and substituted non-GPU backends before dispatch

- rejects Metal and substituted non-GPU backends before dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects Metal and substituted non-GPU backends before dispatch")
expect(x25519_mlkem768_gpu_final_evidence_backend_reason(
    X25519MlKem768EvidenceBackend.Metal)).to_equal(
    "gpu-final-evidence-backend-not-admitted")
expect(x25519_mlkem768_gpu_final_evidence_backend_reason(
    X25519MlKem768EvidenceBackend.Avx2)).to_equal(
    "gpu-final-evidence-backend-not-admitted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 typed GPU final evidence selection.
- X25519MLKEM768 typed GPU final evidence selection

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
- `REQ-010`
- `REQ-013`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8632a3c00d099a98cff618b23eb6aa03b7e6079bb37b75a2fe14c55b692dc12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8632a3c00d099a98cff618b23eb6aa03b7e6079bb37b75a2fe14c55b692dc12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8632a3c00d099a98cff618b23eb6aa03b7e6079bb37b75a2fe14c55b692dc12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.spl
mirror: doc/06_spec/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only CUDA and Vulkan into the same-run typed observation path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/x25519mlkem768_gpu_final_evidence_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects Metal and substituted non-GPU backends before dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
