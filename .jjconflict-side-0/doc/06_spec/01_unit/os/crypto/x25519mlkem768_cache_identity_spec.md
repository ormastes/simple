# X25519mlkem768 Cache Identity Specification

> Tests covering X25519MLKEM768 typed executor cache identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cache Identity Specification

## Scenarios

### X25519MLKEM768 typed executor cache identity

#### should NFR-012 bind version profile configuration source and device

- Bind public provenance before adding the physical device identity
   - Expected: bound.admission_digest.len() equals `64`
   - Expected: bound.key_digest.len() equals `64`
   - Expected: bound.device_identity equals `0`
   - Expected: device_bound.device_identity equals `86`
   - Expected: device_bound.key_digest.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind public provenance before adding the physical device identity")
val initial = x25519_mlkem768_cache_identity(
    "cuda", _CACHE_SOURCE_DIGEST, "")
val bound = match x25519_mlkem768_cache_bind(
        initial, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CACHE_CONFIG_DIGEST):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(bound.bound).to_be(true)
expect(bound.admission_digest.len()).to_equal(64)
expect(bound.key_digest.len()).to_equal(64)
expect(bound.device_identity).to_equal(0)
val device_bound = match x25519_mlkem768_cache_bind_device(bound, 86):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(device_bound.device_identity).to_equal(86)
expect(device_bound.admission_digest).to_equal(
    bound.admission_digest)
expect(device_bound.key_digest.len()).to_equal(64)
expect(device_bound.key_digest == bound.key_digest).to_be(false)
```

</details>

#### should NFR-012 reject reuse across configuration or device identity

- Attempt to reuse one admitted identity with changed public inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt to reuse one admitted identity with changed public inputs")
val initial = x25519_mlkem768_cache_identity(
    "metal", "", _CACHE_ARTIFACT_DIGEST)
val bound = match x25519_mlkem768_cache_bind(
        initial, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CACHE_CONFIG_DIGEST):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(x25519_mlkem768_cache_bind(
    bound, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CACHE_OTHER_CONFIG_DIGEST).is_err()).to_be(true)
val device_bound = match x25519_mlkem768_cache_bind_device(bound, 1):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(x25519_mlkem768_cache_bind_device(
    device_bound, 2).is_err()).to_be(true)
```

</details>

#### should NFR-012 derive distinct keys and reject cross-device mutation

- Bind the same admitted identity independently to two devices
- Mutate a retained device field without recomputing its key


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind the same admitted identity independently to two devices")
val initial = x25519_mlkem768_cache_identity(
    "cuda", _CACHE_SOURCE_DIGEST, "")
val admitted = match x25519_mlkem768_cache_bind(
        initial, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CACHE_CONFIG_DIGEST):
    case Ok(value): value
    case Err(reason): fail(reason)
val device_86 = match x25519_mlkem768_cache_bind_device(admitted, 86):
    case Ok(value): value
    case Err(reason): fail(reason)
val device_87 = match x25519_mlkem768_cache_bind_device(admitted, 87):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(device_86.admission_digest).to_equal(
    device_87.admission_digest)
expect(device_86.key_digest == device_87.key_digest).to_be(false)

step("Mutate a retained device field without recomputing its key")
var cross_device_mutation = device_86
cross_device_mutation.device_identity = 87
match x25519_mlkem768_cache_bind(
        cross_device_mutation,
        X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CACHE_CONFIG_DIGEST):
    case Ok(_): fail("cross-device cache mutation was accepted")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-identity-integrity-mismatch")
```

</details>

#### should NFR-012 reject stale versions and ambiguous artifact identity

- Present stale versions malformed digests and ambiguous provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present stale versions malformed digests and ambiguous provenance")
val source = x25519_mlkem768_cache_identity(
    "cuda", _CACHE_SOURCE_DIGEST, "")
expect(x25519_mlkem768_cache_bind(
    source, "stale", X25519_MLKEM768_PROFILE_VERSION,
    _CACHE_CONFIG_DIGEST).is_err()).to_be(true)
expect(x25519_mlkem768_cache_bind(
    source, X25519_MLKEM768_IMPLEMENTATION_VERSION, "stale",
    _CACHE_CONFIG_DIGEST).is_err()).to_be(true)
val ambiguous = x25519_mlkem768_cache_identity(
    "vulkan", _CACHE_SOURCE_DIGEST, _CACHE_ARTIFACT_DIGEST)
expect(x25519_mlkem768_cache_bind(
    ambiguous, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CACHE_CONFIG_DIGEST).is_err()).to_be(true)
val unknown_backend = x25519_mlkem768_cache_identity(
    "unknown", _CACHE_SOURCE_DIGEST, "")
expect(x25519_mlkem768_cache_bind(
    unknown_backend, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CACHE_CONFIG_DIGEST).is_err()).to_be(true)
val malformed_digest = x25519_mlkem768_cache_identity(
    "cuda", "not-a-sha256-digest", "")
expect(x25519_mlkem768_cache_bind(
    malformed_digest, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CACHE_CONFIG_DIGEST).is_err()).to_be(true)
```

</details>

#### should NFR-012 reject mutated identities and stale unbound state

- Corrupt bound and partially-bound identity fields before reuse


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Corrupt bound and partially-bound identity fields before reuse")
val initial = x25519_mlkem768_cache_identity(
    "cuda", _CACHE_SOURCE_DIGEST, "")
val bound = match x25519_mlkem768_cache_bind(
        initial, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CACHE_CONFIG_DIGEST):
    case Ok(value): value
    case Err(reason): fail(reason)
var mutated = bound
mutated.key_digest = _CACHE_OTHER_CONFIG_DIGEST
match x25519_mlkem768_cache_bind_device(mutated, 1):
    case Ok(_): fail("mutated cache identity was accepted")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-identity-integrity-mismatch")
var stale = initial
stale.configuration_digest = _CACHE_CONFIG_DIGEST
match x25519_mlkem768_cache_bind(
        stale, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CACHE_CONFIG_DIGEST):
    case Ok(_): fail("stale unbound cache state was accepted")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-unbound-state-invalid")
val non_hex =
    "gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg"
expect(x25519_mlkem768_cache_bind(
    initial, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION, non_hex).is_err()).to_be(true)
```

</details>

#### should NFR-012 bind source and binary only through build and device capability

- Bind an exact accelerator build to its source artifact and device capability
   - Expected: device_bound.device_identity equals `86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind an exact accelerator build to its source artifact and device capability")
val linked = x25519_mlkem768_cache_identity(
    "cuda", _CACHE_SOURCE_DIGEST, _CACHE_ARTIFACT_DIGEST,
    _CACHE_BUILD_BINDING_DIGEST, _CACHE_DEVICE_CAPABILITY_DIGEST)
val bound = match x25519_mlkem768_cache_bind(
        linked, X25519_MLKEM768_IMPLEMENTATION_VERSION,
        X25519_MLKEM768_PROFILE_VERSION, _CACHE_CONFIG_DIGEST):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(x25519_mlkem768_cache_bind_device(bound, 86).is_err()).to_be(true)
val device_bound = match x25519_mlkem768_cache_bind_device_capability(
        bound, 86, _CACHE_DEVICE_CAPABILITY_DIGEST):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(device_bound.device_identity).to_equal(86)
expect(x25519_mlkem768_cache_bind_device_capability(
    bound, 86, _CACHE_OTHER_CAPABILITY_DIGEST).is_err()).to_be(true)
val partial = x25519_mlkem768_cache_identity(
    "vulkan", _CACHE_SOURCE_DIGEST, _CACHE_ARTIFACT_DIGEST,
    _CACHE_BUILD_BINDING_DIGEST, "")
expect(x25519_mlkem768_cache_bind(
    partial, X25519_MLKEM768_IMPLEMENTATION_VERSION,
    X25519_MLKEM768_PROFILE_VERSION,
    _CACHE_CONFIG_DIGEST).is_err()).to_be(true)
```

</details>

#### should NFR-012 reject admitted reuse and never bind invalid SPIR-V

- Exercise invalid provider artifacts across changed configurations
- cuda path, file hash sha256
-  cache candidate config
-  cache candidate config
- cuda shutdown
- metal path, file hash sha256
-  cache candidate config
-  cache candidate config
- metal shutdown
-  cache candidate config
-  cache candidate config
- vulkan shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise invalid provider artifacts across changed configurations")
val bytes32 = _cache_bytes32()
val list32 = _cache_list32()

val cuda_path =
    "test/fixtures/crypto/x25519mlkem768/not_a_module.cubin"
var cuda = X25519MlKem768CudaNttExecutor.create_binary(
    cuda_path, file_hash_sha256(cuda_path))
expect(x25519_mlkem768_keygen_cuda_candidate(
    _cache_candidate_config(X25519MlKem768Backend.Cuda, 1),
    cuda, bytes32, list32, list32).is_err()).to_be(true)
expect(cuda.cache_identity.bound).to_be(true)
match x25519_mlkem768_keygen_cuda_candidate(
        _cache_candidate_config(X25519MlKem768Backend.Cuda, 2),
        cuda, bytes32, list32, list32):
    case Ok(_): fail("CUDA reused an executor across configurations")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-key-mismatch")
cuda.shutdown()

val metal_path =
    "test/fixtures/crypto/x25519mlkem768/not_a_library.metallib"
var metal = X25519MlKem768MetalNttExecutor.create_binary(
    metal_path, file_hash_sha256(metal_path))
expect(x25519_mlkem768_keygen_metal_candidate(
    _cache_candidate_config(X25519MlKem768Backend.Metal, 1),
    metal, bytes32, list32, list32).is_err()).to_be(true)
expect(metal.cache_identity.bound).to_be(true)
match x25519_mlkem768_keygen_metal_candidate(
        _cache_candidate_config(X25519MlKem768Backend.Metal, 2),
        metal, bytes32, list32, list32):
    case Ok(_): fail("Metal reused an executor across configurations")
    case Err(reason): expect(reason).to_equal(
        "x25519mlkem768-cache-key-mismatch")
metal.shutdown()

val spirv_path =
    "test/fixtures/crypto/x25519mlkem768/invalid_magic.spv"
val spirv_digest = file_hash_sha256(spirv_path)
var vulkan = X25519MlKem768VulkanNttExecutor.create_binaries(
    spirv_path, spirv_digest, spirv_path, spirv_digest)
expect(x25519_mlkem768_keygen_vulkan_candidate(
    _cache_candidate_config(X25519MlKem768Backend.Vulkan, 1),
    vulkan, bytes32, list32, list32).is_err()).to_be(true)
expect(vulkan.cache_identity.bound).to_be(false)
match x25519_mlkem768_keygen_vulkan_candidate(
        _cache_candidate_config(X25519MlKem768Backend.Vulkan, 2),
        vulkan, bytes32, list32, list32):
    case Ok(_): fail("Vulkan admitted invalid SPIR-V")
    case Err(reason): expect(reason).to_equal(
        "vulkan-ntt-binary-magic-invalid")
vulkan.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_cache_identity_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 typed executor cache identity.
- X25519MLKEM768 typed executor cache identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
