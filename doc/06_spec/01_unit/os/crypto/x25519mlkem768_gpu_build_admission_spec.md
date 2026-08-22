# x25519mlkem768_gpu_build_admission_spec

> Verifies the x25519mlkem768 gpu build admission behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_gpu_build_admission_spec

Verifies the x25519mlkem768 gpu build admission behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the x25519mlkem768 gpu build admission behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### X25519MLKEM768 typed GPU build admission

#### admits exact CUDA and Vulkan build device tuples

- Verify: admits exact CUDA and Vulkan build device tuples
- Bind runner backend accelerator toolchain and stable device


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: admits exact CUDA and Vulkan build device tuples")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects invalid lower hex and stale binding mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects invalid lower hex and stale binding mutation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects backend runner and accelerator artifact substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects backend runner and accelerator artifact substitution")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects unpinned toolchains and malformed live identity shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects unpinned toolchains and malformed live identity shapes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects device capability and stable executor substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects device capability and stable executor substitution")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: keeps Metal fail closed without pinned metallib and live identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: keeps Metal fail closed without pinned metallib and live identity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects uninitialized executors at the live observation boundary
- Require the same admitted executor that owns device state


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-007 REQ-010 REQ-011 REQ-012
step("Verify: rejects uninitialized executors at the live observation boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `95fadb3f767fe62f4ba959b39dea193dd5f00fda171a30a962fa3ae8915074d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95fadb3f767fe62f4ba959b39dea193dd5f00fda171a30a962fa3ae8915074d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95fadb3f767fe62f4ba959b39dea193dd5f00fda171a30a962fa3ae8915074d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_build_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
