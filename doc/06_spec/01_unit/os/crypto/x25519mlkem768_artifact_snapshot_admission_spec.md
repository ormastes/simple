# X25519mlkem768 Artifact Snapshot Admission Specification

> Tests covering X25519MLKEM768 pure accelerator artifact snapshot admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Artifact Snapshot Admission Specification

## Scenarios

### X25519MLKEM768 pure accelerator artifact snapshot admission

#### should NFR-012 enforce CUDA source and binary size boundaries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should NFR-012 enforce CUDA source and binary size boundaries
- Evaluate CUDA artifact sizes without reading a file or opening a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 enforce CUDA source and binary size boundaries")
step("Evaluate CUDA artifact sizes without reading a file or opening a device")
expect(x25519_mlkem768_artifact_size_admitted(
    0, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    _SOURCE_MAX_BYTES, _SOURCE_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _SOURCE_MAX_BYTES + 1, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES + 1,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(false)
```

</details>

#### should NFR-012 enforce Metal source and binary size boundaries

- should NFR-012 enforce Metal source and binary size boundaries
- Evaluate Metal artifact sizes without reading a file or opening a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 enforce Metal source and binary size boundaries")
step("Evaluate Metal artifact sizes without reading a file or opening a device")
expect(x25519_mlkem768_artifact_size_admitted(
    -1, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    1, _SOURCE_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _SOURCE_MAX_BYTES + 1, _SOURCE_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _CUDA_METAL_BINARY_MAX_BYTES + 1,
    _CUDA_METAL_BINARY_MAX_BYTES)).to_be(false)
```

</details>

#### should NFR-012 enforce Vulkan binary size boundaries

- should NFR-012 enforce Vulkan binary size boundaries
- Evaluate paired SPIR-V artifact sizes without reading a file or opening a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 enforce Vulkan binary size boundaries")
step("Evaluate paired SPIR-V artifact sizes without reading a file or opening a device")
expect(x25519_mlkem768_artifact_size_admitted(
    0, _VULKAN_BINARY_MAX_BYTES)).to_be(false)
expect(x25519_mlkem768_artifact_size_admitted(
    1, _VULKAN_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _VULKAN_BINARY_MAX_BYTES,
    _VULKAN_BINARY_MAX_BYTES)).to_be(true)
expect(x25519_mlkem768_artifact_size_admitted(
    _VULKAN_BINARY_MAX_BYTES + 1,
    _VULKAN_BINARY_MAX_BYTES)).to_be(false)
```

</details>

#### should NFR-012 reject short and overlong snapshots for every provider

- should NFR-012 reject short and overlong snapshots for every provider
- Compare admitted metadata with exact short and overlong read lengths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should NFR-012 reject short and overlong snapshots for every provider")
step("Compare admitted metadata with exact short and overlong read lengths")
expect(x25519_mlkem768_artifact_read_exact(
    false, 16, 16)).to_be(false)
expect(x25519_mlkem768_artifact_read_exact(
    true, 16, 15)).to_be(false)
expect(x25519_mlkem768_artifact_read_exact(
    true, 16, 16)).to_be(true)
expect(x25519_mlkem768_artifact_read_exact(
    true, 16, 17)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 pure accelerator artifact snapshot admission.
- X25519MLKEM768 pure accelerator artifact snapshot admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ecda75ec98ac5b2463fade94b9826e4b6a98c5603971ced3f03f1b30637b09b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecda75ec98ac5b2463fade94b9826e4b6a98c5603971ced3f03f1b30637b09b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecda75ec98ac5b2463fade94b9826e4b6a98c5603971ced3f03f1b30637b09b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 enforce CUDA source and binary size boundaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should NFR-012 enforce CUDA source and binary size boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 enforce Metal source and binary size boundaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should NFR-012 enforce Metal source and binary size boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 enforce Vulkan binary size boundaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should NFR-012 enforce Vulkan binary size boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_artifact_snapshot_admission_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should NFR-012 reject short and overlong snapshots for every provider' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
