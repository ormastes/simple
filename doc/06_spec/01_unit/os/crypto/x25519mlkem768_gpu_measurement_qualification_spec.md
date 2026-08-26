# X25519mlkem768 Gpu Measurement Qualification Specification

> Tests covering X25519MLKEM768 fail-closed GPU measurement qualification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Measurement Qualification Specification

## Scenarios

### X25519MLKEM768 fail-closed GPU measurement qualification

#### admits exact CUDA and Vulkan rows and keeps Metal blocked

- Bind qualification execution lifecycle and canonical build tuple
- qualification,  gpu config


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind qualification execution lifecycle and canonical build tuple")
for backend in [X25519MlKem768EvidenceBackend.Cuda,
        X25519MlKem768EvidenceBackend.Vulkan]:
    val qualification = _gpu_qualification(backend)
    expect(_gpu_reason(
        qualification, _gpu_config(qualification),
        _gpu_evidence(qualification), _gpu_delta())).to_equal("")
val metal = _gpu_qualification(X25519MlKem768EvidenceBackend.Metal)
expect(_gpu_reason(metal, _gpu_config(metal),
    _gpu_evidence(metal), _gpu_delta())).to_equal(
    "gpu-build-metal-metallib-and-live-identity-not-pinned")
```

</details>

#### rejects invalid qualification policy version and batch first

- invalid,  gpu config
- var suggest =  gpu config
- var wrong version =  gpu config
- var bad batch =  gpu config


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _gpu_qualification(
    X25519MlKem768EvidenceBackend.Cuda)
val evidence = _gpu_evidence(qualification)
var invalid = qualification
invalid.qualification_sha256 = "0" * 64
expect(_gpu_reason(
    invalid, _gpu_config(qualification), evidence,
    _gpu_delta())).to_equal("gpu-measurement-qualification-invalid")

var suggest = _gpu_config(qualification)
suggest.selection_mode = X25519MlKem768SelectionMode.Suggest
expect(_gpu_reason(
    qualification, suggest, evidence, _gpu_delta())).to_equal(
    "gpu-measurement-config-policy-mismatch")

var wrong_version = _gpu_config(qualification)
wrong_version.profile_version = "wrong"
expect(_gpu_reason(
    qualification, wrong_version, evidence, _gpu_delta())).to_equal(
    "gpu-measurement-config-version-mismatch")

var bad_batch = _gpu_config(qualification)
bad_batch.minimum_batch = bad_batch.batch_size + 1
expect(_gpu_reason(
    qualification, bad_batch, evidence, _gpu_delta())).to_equal(
    "gpu-measurement-config-batch-mismatch")
```

</details>

#### rejects execution substitution fallback and lifecycle gaps

- var invalid delta =  gpu delta


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _gpu_qualification(
    X25519MlKem768EvidenceBackend.Cuda)
val config = _gpu_config(qualification)
val evidence = _gpu_evidence(qualification)

var wrong_backend = evidence
wrong_backend.selected_backend = X25519MlKem768Backend.Vulkan
expect(_gpu_reason(
    qualification, config, wrong_backend, _gpu_delta())).to_equal(
    "gpu-measurement-executed-backend-mismatch")

var wrong_artifact = evidence
wrong_artifact.artifact_digest = "8" * 64
expect(_gpu_reason(
    qualification, config, wrong_artifact, _gpu_delta())).to_equal(
    "gpu-measurement-execution-binding-mismatch")

var wrong_device = evidence
wrong_device.executor_identity = "cuda-device:99"
expect(_gpu_reason(
    qualification, config, wrong_device, _gpu_delta())).to_equal(
    "gpu-measurement-device-identity-mismatch")

var fallback = evidence
fallback.fallback_used = true
expect(_gpu_reason(
    qualification, config, fallback, _gpu_delta())).to_equal(
    "gpu-measurement-fallback-or-oracle-mismatch")

var incomplete = evidence
incomplete.device_readback = false
expect(_gpu_reason(
    qualification, config, incomplete, _gpu_delta())).to_equal(
    "gpu-measurement-device-lifecycle-incomplete")

var invalid_delta = _gpu_delta()
invalid_delta.readback_count = 2
expect(_gpu_reason(
    qualification, config, evidence, invalid_delta)).to_equal(
    "gpu-measurement-lifecycle-delta-invalid")

var wrong_count = evidence
wrong_count.kernel_invocations = 4
expect(_gpu_reason(
    qualification, config, wrong_count, _gpu_delta())).to_equal(
    "gpu-measurement-kernel-count-mismatch")
```

</details>

#### rejects forged cross-runner and cross-device build admissions

- var runner =  gpu admission for
- var device =  gpu admission for


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qualification = _gpu_qualification(
    X25519MlKem768EvidenceBackend.Cuda)
val config = _gpu_config(qualification)
val evidence = _gpu_evidence(qualification)
var runner = _gpu_admission_for(qualification)
runner.runner_artifact_sha256 = "2" * 64
expect(x25519_mlkem768_qualified_gpu_measurement_reason(
    qualification, config, runner, evidence, _gpu_delta())).to_equal(
    "gpu-build-qualification-runner-artifact-mismatch")
var device = _gpu_admission_for(qualification)
device.live_device_identity_tag = 99
device.live_device_identity = "cuda-device-identity:99"
expect(x25519_mlkem768_qualified_gpu_measurement_reason(
    qualification, config, device, evidence, _gpu_delta())).to_equal(
    "gpu-build-qualification-stable-executor-identity-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_gpu_measurement_qualification_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 fail-closed GPU measurement qualification.
- X25519MLKEM768 fail-closed GPU measurement qualification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
