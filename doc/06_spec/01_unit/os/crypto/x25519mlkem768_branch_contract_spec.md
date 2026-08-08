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

- Submit a one-coefficient batch to every GPU provider
   - Expected: cuda_result.reason equals `cuda-ntt-input-size-invalid`
- cuda shutdown
   - Expected: reason equals `metal-ntt-input-size-invalid`
- metal shutdown
   - Expected: reason equals `vulkan-ntt-input-size-invalid`
- vulkan shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Submit compiled artifacts without their pinned digests
   - Expected: cuda_result.reason equals `cuda-ntt-binary-digest-mismatch`
- cuda shutdown
   - Expected: reason equals `metal-ntt-binary-digest-mismatch`
- metal shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Admit a digest-matched source that lacks CUDA entry points
- executor,  branch list
   - Expected: result.reason equals `cuda-ntt-artifact-invalid`
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Exercise digest mismatch and invalid SPIR-V magic independently
   - Expected: reason equals `vulkan-ntt-binary-digest-mismatch`
- mismatch shutdown
   - Expected: reason equals `vulkan-ntt-binary-magic-invalid`
- invalid magic shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Close the executor before submitting a valid-size batch
- executor shutdown
- executor,  branch list
   - Expected: reason equals `vulkan-ntt-executor-closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Request CUDA through the Vulkan-only candidate resolver
-  branch config


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Submit malformed secondary key material to CUDA and Metal candidates
-  branch config
-  branch config
-  branch config
- cuda shutdown
-  branch config
-  branch config
-  branch config
- metal shutdown
-  branch config
-  branch config
-  branch config
- vulkan shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-08-05 |
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
