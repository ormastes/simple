# X25519mlkem768 Gpu Dispatch Contract Specification

> Tests covering X25519MLKEM768 exact-binary GPU dispatch contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Dispatch Contract Specification

## Scenarios

### X25519MLKEM768 exact-binary GPU dispatch contract

#### should reject a non-GPU backend before artifact admission

- Dispatch a scalar row through the GPU-only entry point
-  request
   - Expected: result.exit_code equals `1`
   - Expected: result.receipt.reason equals `gpu-dispatch-backend-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a scalar row through the GPU-only entry point")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.ScalarCpu))
expect(result.exit_code).to_equal(1)
expect(result.receipt.status).to_equal(
    X25519MlKem768EvidenceStatus.Blocked)
expect(result.receipt.reason).to_equal("gpu-dispatch-backend-invalid")
expect(result.receipt.selected_backend).to_be_nil()
expect(result.receipt.promotion_eligible).to_be(false)
expect(result.receipt.fallback_used).to_be(false)
```

</details>

#### should preserve the pinned Metal exact-binary blocker

- Dispatch Metal without an admitted metallib identity
-  request
   - Expected: result.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch Metal without an admitted metallib identity")
val result = x25519_mlkem768_dispatch_gpu(
    _request(X25519MlKem768EvidenceBackend.Metal))
expect(result.exit_code).to_equal(1)
expect(result.receipt.status).to_equal(
    X25519MlKem768EvidenceStatus.Blocked)
expect(result.receipt.reason).to_equal(
    "metal-binary-digest-not-pinned-by-fixture-manifest")
expect(result.receipt.compiled).to_be(false)
expect(result.receipt.submitted).to_be(false)
expect(result.receipt.fence_completed).to_be(false)
expect(result.receipt.device_readback).to_be(false)
```

</details>

#### should reject zero and oversized GPU batches before artifact admission

- var zero =  request
- var oversized =  request


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var zero = _request(X25519MlKem768EvidenceBackend.Vulkan)
zero.evidence.batch_size = 0
val zero_result = x25519_mlkem768_dispatch_gpu(zero)
expect(zero_result.receipt.reason).to_equal(
    "gpu-batch-size-must-be-in-1..1024")
var oversized = _request(X25519MlKem768EvidenceBackend.Cuda)
oversized.evidence.batch_size = 1025
val oversized_result = x25519_mlkem768_dispatch_gpu(oversized)
expect(oversized_result.receipt.reason).to_equal(
    "gpu-batch-size-must-be-in-1..1024")
```

</details>

#### should bind admission to live CUDA and Vulkan device identity

- Inspect fail-closed CUDA capability and device-name gates
- Inspect the fail-closed Vulkan driver and API gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect fail-closed CUDA capability and device-name gates")
val source = file_read_text(_DISPATCH_SOURCE)
expect(source).to_contain(
    "observed_capability != admission.device_capability")
expect(source).to_contain("observed_name != admission.device_name")
step("Inspect the fail-closed Vulkan driver and API gate")
expect(source).to_contain(
    "executor.session.device_name != admission.device_name")
expect(source).to_contain("executor.session.device_identity <= 0")
expect(source).to_contain(
    "executor.session.driver_identity")
expect(source).to_contain("not identity.contains(\"|vendor=\")")
expect(source).to_contain("not identity.contains(\"|device=\")")
expect(source).to_contain("not identity.contains(\"|driver=\")")
expect(source).to_contain("not identity.contains(\"|api=\")")
expect(source).to_contain(
    "vulkan-runtime-api-version-not-admitted")
expect(source).to_contain("00401000")
expect(source).to_contain("00404000")
```

</details>

#### should bind each device run to exact admitted artifacts and one identity

- Inspect exact CUDA and Vulkan binary-set proof checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect exact CUDA and Vulkan binary-set proof checks")
val source = file_read_text(_DISPATCH_SOURCE)
expect(source).to_contain(
    "outputs.execution_proof_digest != admission.binary_sha256")
expect(source).to_contain(
    "outputs.execution_proof_digest != artifact_set_digest")
expect(source).to_contain("cuda-executor-identity-changed")
expect(source).to_contain("cuda-executed-artifact-changed")
expect(source).to_contain("vulkan-runtime-device-identity-changed")
expect(source).to_contain("vulkan-executor-identity-changed")
expect(source).to_contain("vulkan-full-executor-identity-invalid")
```

</details>

#### should require positive batches complete lifecycle and absolute oracles

- Inspect batch, lifecycle, fallback, and oracle gates
- "sha256 text
- "sha256 text
- "sha256 text


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect batch, lifecycle, fallback, and oracle gates")
val source = file_read_text(_DISPATCH_SOURCE)
expect(source).to_contain("cuda-positive-batch-required")
expect(source).to_contain("vulkan-positive-batch-required")
expect(source).to_contain(
    "X25519MlKem768VerificationPolicy.AbsoluteAndScalar")
expect(source).to_contain("not outputs.candidate_oracle_match")
expect(source).to_contain("outputs.fallback_used")
expect(source).to_contain("not outputs.compiled")
expect(source).to_contain("not outputs.submitted")
expect(source).to_contain("not outputs.fence_completed")
expect(source).to_contain("not outputs.device_readback")
expect(source).to_contain("outputs.accelerated_operation_count != 3")
expect(source).to_contain(
    "kernel_invocations < request.evidence.batch_size * 3")
expect(source).to_contain(
    "request.evidence.batch_size > X25519_MLKEM768_EVIDENCE_MAX_BATCH")
expect(source).to_contain(
    "sha256_text(keygen_digest_chain)")
expect(source).to_contain(
    "sha256_text(encapsulate_digest_chain)")
expect(source).to_contain(
    "sha256_text(decapsulate_digest_chain)")
```

</details>

#### should expose no scalar-bypass or promotion authority

- Inspect the complete public surface and promotion boundary
   - Expected: source.split("\nexport ").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the complete public surface and promotion boundary")
val source = file_read_text(_DISPATCH_SOURCE)
expect(source).to_contain(
    "export X25519MlKem768GpuDispatchRequest, X25519MlKem768GpuDispatchResult\n" +
    "export x25519_mlkem768_dispatch_gpu")
expect(source.split("\nexport ").len()).to_equal(3)
expect(source.contains("export _cuda_roundtrip")).to_be(false)
expect(source.contains("export _vulkan_roundtrip")).to_be(false)
expect(source.contains("verify_scalar")).to_be(false)
expect(source.contains("qualified_cuda_measurement")).to_be(false)
expect(source.contains("qualified_vulkan_measurement")).to_be(false)
expect(source.contains("VerificationPolicy.None")).to_be(false)
expect(source).to_contain("promotion_eligible: false")
expect(source).to_contain("receipt.promotion_eligible = false")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_gpu_dispatch_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 exact-binary GPU dispatch contract.
- X25519MLKEM768 exact-binary GPU dispatch contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
