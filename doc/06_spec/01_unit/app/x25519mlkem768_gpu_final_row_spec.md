# X25519mlkem768 Gpu Final Row Specification

> Tests covering X25519MLKEM768 GPU final-row adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Final Row Specification

## Scenarios

### X25519MLKEM768 GPU final-row adapter

#### composes exactly one CUDA and Vulkan executed row from pinned outputs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- composes exactly one CUDA and Vulkan executed row from pinned outputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("composes exactly one CUDA and Vulkan executed row from pinned outputs")
val cuda = x25519_mlkem768_compose_gpu_final_matrix_row(
    _receipt(X25519MlKem768EvidenceBackend.Cuda),
    _outputs(X25519MlKem768EvidenceBackend.Cuda), _ARTIFACT, _ARTIFACT,
    "linux", "x86_64")
expect(cuda.is_ok()).to_be(true)
expect(cuda.unwrap().execution.promotion_eligible).to_be(true)
val vulkan = x25519_mlkem768_compose_gpu_final_matrix_row(
    _receipt(X25519MlKem768EvidenceBackend.Vulkan),
    _outputs(X25519MlKem768EvidenceBackend.Vulkan), _ARTIFACT, _ARTIFACT,
    "linux", "x86_64")
expect(vulkan.is_ok()).to_be(true)
expect(vulkan.unwrap().admission_phase).to_equal(
    X25519MlKem768MatrixAdmissionPhase.Executed)
```

</details>

#### rejects non-native raw receipts and Metal

- rejects non-native raw receipts and Metal


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects non-native raw receipts and Metal")
var emulated = _receipt(X25519MlKem768EvidenceBackend.Cuda)
emulated.mode = X25519MlKem768EvidenceMode.QemuCorrectness
emulated.emulated = true
_expect_err(x25519_mlkem768_compose_gpu_final_matrix_row(
    emulated, _outputs(X25519MlKem768EvidenceBackend.Cuda),
    _ARTIFACT, _ARTIFACT, "linux", "x86_64"),
    "gpu-final-row-requires-native-full-operation")
_expect_err(x25519_mlkem768_compose_gpu_final_matrix_row(
    _receipt(X25519MlKem768EvidenceBackend.Metal),
    _outputs(X25519MlKem768EvidenceBackend.Vulkan),
    _ARTIFACT, _ARTIFACT, "macos", "x86_64"),
    "gpu-final-row-backend-not-admitted")
```

</details>

#### rejects missing A/B/C identity and tampered operation binding

- rejects missing A/B/C identity and tampered operation binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects missing A/B/C identity and tampered operation binding")
var missing_set = _outputs(X25519MlKem768EvidenceBackend.Cuda)
missing_set.set_c.set_id = X25519MlKem768PinnedSet.MlKem
_expect_err(x25519_mlkem768_compose_gpu_final_matrix_row(
    _receipt(X25519MlKem768EvidenceBackend.Cuda), missing_set,
    _ARTIFACT, _ARTIFACT, "linux", "x86_64"),
    "gpu-final-row-public-set-identity-mismatch")
var tampered = _receipt(X25519MlKem768EvidenceBackend.Vulkan)
tampered.keygen_output_digest = "0" * 64
_expect_err(x25519_mlkem768_compose_gpu_final_matrix_row(
    tampered, _outputs(X25519MlKem768EvidenceBackend.Vulkan),
    _ARTIFACT, _ARTIFACT, "linux", "x86_64"),
    "gpu-final-row-operation-output-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/x25519mlkem768_gpu_final_row_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 GPU final-row adapter.
- X25519MLKEM768 GPU final-row adapter

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

- `REQ-SSPEC-UNIT`
- `REQ-003`
- `REQ-010`
- `REQ-013`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e68dd3c10b692fc2f2da8b442b98b69107790172069c1fbc83a06c570d83fe71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e68dd3c10b692fc2f2da8b442b98b69107790172069c1fbc83a06c570d83fe71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e68dd3c10b692fc2f2da8b442b98b69107790172069c1fbc83a06c570d83fe71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/x25519mlkem768_gpu_final_row_spec.spl
mirror: doc/06_spec/01_unit/app/x25519mlkem768_gpu_final_row_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/x25519mlkem768_gpu_final_row_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/x25519mlkem768_gpu_final_row_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/x25519mlkem768_gpu_final_row_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/x25519mlkem768_gpu_final_row_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'composes exactly one CUDA and Vulkan executed row from pinned outputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/x25519mlkem768_gpu_final_row_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-native raw receipts and Metal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/x25519mlkem768_gpu_final_row_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects missing A/B/C identity and tampered operation binding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
