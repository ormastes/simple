# X25519mlkem768 Branch Contract Specification

> Tests covering X25519MLKEM768 deterministic branch contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Branch Contract Specification

## Scenarios

### X25519MLKEM768 deterministic branch contract

#### should reject non-multiple batches before GPU initialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject non-multiple batches before GPU initialization
- Submit a one-coefficient batch to every GPU provider
   - Expected: cuda_result.reason equals `cuda-ntt-input-size-invalid`
   - Expected: reason equals `metal-ntt-input-size-invalid`
   - Expected: reason equals `vulkan-ntt-input-size-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject non-multiple batches before GPU initialization")
step("Submit a one-coefficient batch to every GPU provider")
val malformed = [17]
var cuda = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
val cuda_result = x25519_mlkem768_cuda_ntt_execute(cuda, malformed)
expect(cuda_result.completed).to_be(false)
expect(cuda_result.reason).to_equal("cuda-ntt-input-size-invalid")
cuda.shutdown()

var metal = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
match x25519_mlkem768_metal_ntt_execute(metal, malformed):
    case Ok(_): fail("Metal accepted a non-multiple batch")
    case Err(reason):
        expect(reason).to_equal("metal-ntt-input-size-invalid")
metal.shutdown()

var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "", "missing-inverse.spv", "")
match x25519_mlkem768_vulkan_ntt_execute(vulkan, malformed):
    case Ok(_): fail("Vulkan accepted a non-multiple batch")
    case Err(reason):
        expect(reason).to_equal("vulkan-ntt-input-size-invalid")
vulkan.shutdown()
```

</details>

#### should reject unpinned CUDA and Metal binary bytes before hardware

- should reject unpinned CUDA and Metal binary bytes before hardware
- Submit compiled artifacts without their pinned digests
   - Expected: cuda_result.reason equals `cuda-ntt-binary-digest-mismatch`
   - Expected: reason equals `metal-ntt-binary-digest-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject unpinned CUDA and Metal binary bytes before hardware")
step("Submit compiled artifacts without their pinned digests")
val fixture = _branch_list(256)
var cuda = X25519MlKem768CudaNttExecutor.create_binary(
    _BRANCH_INVALID_CUBIN, "")
val cuda_result = x25519_mlkem768_cuda_ntt_execute(cuda, fixture)
expect(cuda_result.completed).to_be(false)
expect(cuda_result.reason).to_equal("cuda-ntt-binary-digest-mismatch")
cuda.shutdown()

var metal = X25519MlKem768MetalNttExecutor.create_binary(
    _BRANCH_INVALID_METALLIB, "")
match x25519_mlkem768_metal_ntt_execute(metal, fixture):
    case Ok(_): fail("Metal accepted an unpinned metallib")
    case Err(reason):
        expect(reason).to_equal("metal-ntt-binary-digest-mismatch")
metal.shutdown()
```

</details>

#### should reject CUDA source without both entry points after digest admission

- should reject CUDA source without both entry points after digest admission
- Admit a digest-matched source that lacks CUDA entry points
   - Expected: result.reason equals `cuda-ntt-artifact-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject CUDA source without both entry points after digest admission")
step("Admit a digest-matched source that lacks CUDA entry points")
var executor = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
executor.expected_source_digest = executor.source_digest
val result = x25519_mlkem768_cuda_ntt_execute(
    executor, _branch_list(256))
expect(result.completed).to_be(false)
expect(result.reason).to_equal("cuda-ntt-artifact-invalid")
executor.shutdown()
```

</details>

#### should reject Vulkan digest and magic failures before initialization

- should reject Vulkan digest and magic failures before initialization
- Exercise digest mismatch and invalid SPIR-V magic independently
   - Expected: reason equals `vulkan-ntt-binary-digest-mismatch`
   - Expected: reason equals `vulkan-ntt-binary-magic-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject Vulkan digest and magic failures before initialization")
step("Exercise digest mismatch and invalid SPIR-V magic independently")
val fixture = _branch_list(256)
var mismatch = X25519MlKem768VulkanNttExecutor.create_binaries(
    _BRANCH_INVALID_SPIRV, "wrong-forward-digest",
    _BRANCH_INVALID_SPIRV, "wrong-inverse-digest")
match x25519_mlkem768_vulkan_ntt_execute(mismatch, fixture):
    case Ok(_): fail("Vulkan accepted mismatched SPIR-V digests")
    case Err(reason):
        expect(reason).to_equal("vulkan-ntt-binary-digest-mismatch")
mismatch.shutdown()

val digest = file_hash_sha256(_BRANCH_INVALID_SPIRV)
var invalid_magic = X25519MlKem768VulkanNttExecutor.create_binaries(
    _BRANCH_INVALID_SPIRV, digest,
    _BRANCH_INVALID_SPIRV, digest)
match x25519_mlkem768_vulkan_ntt_execute(invalid_magic, fixture):
    case Ok(_): fail("Vulkan accepted invalid SPIR-V magic")
    case Err(reason):
        expect(reason).to_equal("vulkan-ntt-binary-magic-invalid")
invalid_magic.shutdown()
```

</details>

#### should reject Vulkan use after shutdown before artifact access

- should reject Vulkan use after shutdown before artifact access
- Close the executor before submitting a valid-size batch
   - Expected: reason equals `vulkan-ntt-executor-closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject Vulkan use after shutdown before artifact access")
step("Close the executor before submitting a valid-size batch")
var executor = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "", "missing-inverse.spv", "")
executor.shutdown()
match x25519_mlkem768_vulkan_ntt_execute(
        executor, _branch_list(256)):
    case Ok(_): fail("Vulkan executor ran after shutdown")
    case Err(reason):
        expect(reason).to_equal("vulkan-ntt-executor-closed")
```

</details>

#### should reject a non-Vulkan backend in the Vulkan resolver

- should reject a non-Vulkan backend in the Vulkan resolver
- Request CUDA through the Vulkan-only candidate resolver


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject a non-Vulkan backend in the Vulkan resolver")
step("Request CUDA through the Vulkan-only candidate resolver")
match x25519_mlkem768_resolve_vulkan_candidate(
        _branch_config(X25519MlKem768Backend.Cuda), "keygen"):
    case Ok(_): fail("Vulkan resolver accepted CUDA")
    case Err(reason):
        expect(reason).to_equal(
            "requested backend is not the Vulkan candidate")
```

</details>

#### should reject secondary GPU key-material guards before provider access

- should reject secondary GPU key-material guards before provider access
- Submit malformed secondary key material to CUDA and Metal candidates


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject secondary GPU key-material guards before provider access")
step("Submit malformed secondary key material to CUDA and Metal candidates")
val private_key = _branch_bytes32()
val seed = _branch_list(32)
val client_share = _branch_list(1216)
val server_share = _branch_list(1120)

var cuda = X25519MlKem768CudaNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx")
match x25519_mlkem768_keygen_cuda_candidate(
        _branch_config(X25519MlKem768Backend.Cuda), cuda,
        private_key, [], seed):
    case Ok(_): fail("CUDA keygen accepted a short seed")
    case Err(reason): expect(reason).to_contain("three 32-byte inputs")
match x25519_mlkem768_encapsulate_cuda_candidate(
        _branch_config(X25519MlKem768Backend.Cuda), cuda,
        client_share, [], seed):
    case Ok(_): fail("CUDA encapsulation accepted a short private key")
    case Err(reason): expect(reason).to_contain("32-byte inputs")
match x25519_mlkem768_decapsulate_cuda_candidate(
        _branch_config(X25519MlKem768Backend.Cuda), cuda,
        server_share, private_key, []):
    case Ok(_): fail("CUDA decapsulation accepted a short key")
    case Err(reason): expect(reason).to_contain("invalid key sizes")
cuda.shutdown()

var metal = X25519MlKem768MetalNttExecutor.create(
    "src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt.metal")
match x25519_mlkem768_keygen_metal_candidate(
        _branch_config(X25519MlKem768Backend.Metal), metal,
        private_key, [], seed):
    case Ok(_): fail("Metal keygen accepted a short seed")
    case Err(reason): expect(reason).to_contain("three 32-byte inputs")
match x25519_mlkem768_encapsulate_metal_candidate(
        _branch_config(X25519MlKem768Backend.Metal), metal,
        client_share, [], seed):
    case Ok(_): fail("Metal encapsulation accepted a short private key")
    case Err(reason): expect(reason).to_contain("32-byte inputs")
match x25519_mlkem768_decapsulate_metal_candidate(
        _branch_config(X25519MlKem768Backend.Metal), metal,
        server_share, private_key, []):
    case Ok(_): fail("Metal decapsulation accepted a short key")
    case Err(reason): expect(reason).to_contain("invalid key sizes")
metal.shutdown()

var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    "missing-forward.spv", "", "missing-inverse.spv", "")
match x25519_mlkem768_keygen_vulkan_candidate(
        _branch_config(X25519MlKem768Backend.Vulkan), vulkan,
        private_key, [], seed):
    case Ok(_): fail("Vulkan keygen accepted a short seed")
    case Err(reason): expect(reason).to_contain("three 32-byte inputs")
match x25519_mlkem768_encapsulate_vulkan_candidate(
        _branch_config(X25519MlKem768Backend.Vulkan), vulkan,
        client_share, [], seed):
    case Ok(_): fail("Vulkan encapsulation accepted a short private key")
    case Err(reason): expect(reason).to_contain("32-byte inputs")
match x25519_mlkem768_decapsulate_vulkan_candidate(
        _branch_config(X25519MlKem768Backend.Vulkan), vulkan,
        server_share, private_key, []):
    case Ok(_): fail("Vulkan decapsulation accepted a short key")
    case Err(reason): expect(reason).to_contain("invalid key sizes")
vulkan.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 deterministic branch contract.
- X25519MLKEM768 deterministic branch contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `4094365ae29552ec2c73e8ee99d2f1211dbfe80860b97177db52848f011f35e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4094365ae29552ec2c73e8ee99d2f1211dbfe80860b97177db52848f011f35e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4094365ae29552ec2c73e8ee99d2f1211dbfe80860b97177db52848f011f35e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject non-multiple batches before GPU initialization' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject non-multiple batches before GPU initialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject unpinned CUDA and Metal binary bytes before hardware' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject unpinned CUDA and Metal binary bytes before hardware' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:125:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject CUDA source without both entry points after digest admission' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject CUDA source without both entry points after digest admission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:138:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject Vulkan digest and magic failures before initialization' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:162:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject Vulkan use after shutdown before artifact access' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_branch_contract_spec.spl:175:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a non-Vulkan backend in the Vulkan resolver' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
