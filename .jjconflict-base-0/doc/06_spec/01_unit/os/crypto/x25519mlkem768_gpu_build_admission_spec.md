# X25519mlkem768 Gpu Build Admission Specification

> Tests covering X25519MLKEM768 typed GPU build admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Build Admission Specification

## Scenarios

### X25519MLKEM768 typed GPU build admission

#### admits exact CUDA and Vulkan build device tuples

- Bind runner backend accelerator toolchain and stable device


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind runner backend accelerator toolchain and stable device")
val cuda = _cuda_admission()
val vulkan = _vulkan_admission()
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(cuda), cuda)).to_equal("")
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(vulkan), vulkan)).to_equal("")
```

</details>

#### rejects invalid lower hex and stale binding mutation

- var upper =  target
- var mutated =  target


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = _cuda_admission()
var upper = _target(cuda)
upper.accelerator_build_binding_sha256 = "A" * 64
expect(x25519_mlkem768_gpu_build_admission_reason(
    upper, cuda)).to_equal("gpu-build-binding-sha256-invalid")

var mutated = _target(cuda)
mutated.accelerator_build_binding_sha256 = "3" * 64
expect(x25519_mlkem768_gpu_build_admission_reason(
    mutated, cuda)).to_equal("gpu-build-binding-sha256-mismatch")

var malformed = cuda
malformed.accelerator_binary_sha256 = "B" * 64
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(malformed), malformed)).to_equal(
        "gpu-build-accelerator-binary-sha256-invalid")
```

</details>

#### rejects backend runner and accelerator artifact substitution

- var backend =  target
- var runner =  target
- var artifact =  target
- var vulkan aux =  vulkan admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = _cuda_admission()
var backend = _target(cuda)
backend.backend = X25519MlKem768EvidenceBackend.Vulkan
expect(x25519_mlkem768_gpu_build_admission_reason(
    backend, cuda)).to_equal("gpu-build-qualification-backend-mismatch")

var runner = _target(cuda)
runner.runner_artifact_sha256 = "4" * 64
expect(x25519_mlkem768_gpu_build_admission_reason(
    runner, cuda)).to_equal(
    "gpu-build-qualification-runner-artifact-mismatch")

var artifact = _target(cuda)
artifact.backend_artifact_sha256 = "5" * 64
expect(x25519_mlkem768_gpu_build_admission_reason(
    artifact, cuda)).to_equal(
    "gpu-build-qualification-backend-artifact-mismatch")

var vulkan_aux = _vulkan_admission()
vulkan_aux.accelerator_binary_aux_sha256 = "6" * 64
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(vulkan_aux), vulkan_aux)).to_equal(
        "gpu-build-vulkan-binary-set-mismatch")
```

</details>

#### rejects unpinned toolchains and malformed live identity shapes

- var cuda toolchain =  cuda admission
- var cuda identity =  cuda admission
- var vulkan toolchain =  vulkan admission
- var vulkan identity =  vulkan admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cuda_toolchain = _cuda_admission()
cuda_toolchain.build_toolchain = "CUDA ptxas 13.0"
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(cuda_toolchain), cuda_toolchain)).to_equal(
        "gpu-build-cuda-toolchain-mismatch")

var cuda_identity = _cuda_admission()
cuda_identity.live_device_identity = "cuda-device-identity:1"
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(cuda_identity), cuda_identity)).to_equal(
        "gpu-build-cuda-live-device-identity-invalid")

var vulkan_toolchain = _vulkan_admission()
vulkan_toolchain.build_toolchain = "glslangValidator"
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(vulkan_toolchain), vulkan_toolchain)).to_equal(
        "gpu-build-vulkan-toolchain-mismatch")

var vulkan_identity = _vulkan_admission()
vulkan_identity.live_device_identity = "NVIDIA TITAN RTX"
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(vulkan_identity), vulkan_identity)).to_equal(
        "gpu-build-vulkan-live-device-identity-invalid")
```

</details>

#### rejects device capability and stable executor substitution

- var device =  cuda admission
- var identity =  target


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var device = _cuda_admission()
device.device_capability = "7.5"
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(device), device)).to_equal(
        "gpu-build-cuda-device-capability-mismatch")

val vulkan = _vulkan_admission()
var identity = _target(vulkan)
identity.executor_identity = "vulkan-device:99:spirv-set:" +
    vulkan.backend_artifact_sha256 + ":cache:" +
    vulkan.executor_cache_identity_sha256
expect(x25519_mlkem768_gpu_build_admission_reason(
    identity, vulkan)).to_equal(
        "gpu-build-qualification-stable-executor-identity-mismatch")
```

</details>

#### keeps Metal fail closed without pinned metallib and live identity

- var metal =  cuda admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var metal = _cuda_admission()
metal.backend = X25519MlKem768EvidenceBackend.Metal
metal.build_toolchain = "Apple Metal compiler"
metal.device_capability = "metal3"
metal.device_name = "Apple GPU"
metal.live_device_identity = "metal-device:Apple GPU"
expect(x25519_mlkem768_gpu_build_admission_reason(
    _target(metal), metal)).to_equal(
    "gpu-build-metal-metallib-and-live-identity-not-pinned")
```

</details>

#### rejects uninitialized executors at the live observation boundary

- Require the same admitted executor that owns device state


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the same admitted executor that owns device state")
val cuda = X25519MlKem768CudaNttExecutor.create_binary(
    "test/fixtures/crypto/x25519mlkem768/not_a_module.cubin",
    "1" * 64)
match x25519_mlkem768_observe_cuda_gpu_build_admission(
        cuda, "2" * 64):
    case Ok(_): fail("uninitialized CUDA executor was observed")
    case Err(reason): expect(reason).to_equal(
        "gpu-build-cuda-live-executor-not-admitted")
val vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "test/fixtures/crypto/x25519mlkem768/invalid_magic.spv",
    "3" * 64,
    "test/fixtures/crypto/x25519mlkem768/invalid_magic.spv",
    "4" * 64)
match x25519_mlkem768_observe_vulkan_gpu_build_admission(
        vulkan, "2" * 64):
    case Ok(_): fail("uninitialized Vulkan executor was observed")
    case Err(reason): expect(reason).to_equal(
        "gpu-build-vulkan-live-executor-not-admitted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 typed GPU build admission.
- X25519MLKEM768 typed GPU build admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
