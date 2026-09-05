# X25519mlkem768 Vulkan Candidate Specification

> Tests covering X25519MLKEM768 Vulkan full candidate facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Vulkan Candidate Specification

## Scenarios

### X25519MLKEM768 Vulkan full candidate facade

#### should run the exact pinned A B C fixture or retain its physical blocker

- Construct one executor from the retained forward and inverse SPIR-V
- defer executor shutdown
-  pinned vulkan config
   - Expected: executor.zeta_bytes.len() equals `512`
   - Expected: executor.zeta_encoding_count equals `1`
- Retain the exact binary-admission blocker
- Retain physical Vulkan unavailability without a fake pass
- Require exact same-data output and device lifecycle evidence
   - Expected: outputs.accelerated_operation_count equals `3`
   - Expected: outputs.kernel_invocations equals `7`
   - Expected: executor.session.generation equals `1`
   - Expected: executor.zeta_encoding_count equals `1`
- Reject the adjacent invalid operation without stale fence state


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct one executor from the retained forward and inverse SPIR-V")
var executor = X25519MlKem768VulkanNttExecutor.create_binaries(
    "build/evidence/x25519mlkem768/vulkan/x25519mlkem768_ntt_forward.spv",
    "0865f588f0825a3ff66a1d5e2cd2a9d0c356bb75b4fceaaf5c2196ffa05f6379",
    "build/evidence/x25519mlkem768/vulkan/x25519mlkem768_ntt_inverse.spv",
    "07a11b541ef204a4fb6c907338dafc99bdf870d2046edcfad02a3d42dcca2687")
defer executor.shutdown()
val result = x25519_mlkem768_run_pinned_vulkan_workload(
    _pinned_vulkan_config(), executor)
expect(executor.zeta_bytes.len()).to_equal(512)
expect(executor.zeta_encoding_count).to_equal(1)
if executor.admission_reason != "":
    step("Retain the exact binary-admission blocker")
    match result:
        case Ok(_): fail("Vulkan ran without admitted exact SPIR-V")
        case Err(reason): expect(reason).to_equal(
            "pinned-set-a-vulkan-keygen:" + executor.admission_reason)
elif not vulkan_sffi_is_available():
    step("Retain physical Vulkan unavailability without a fake pass")
    match result:
        case Ok(_): fail("Unavailable Vulkan returned execution evidence")
        case Err(reason): expect(reason).to_equal(
            "pinned-set-a-vulkan-keygen:vulkan-unavailable")
else:
    step("Require exact same-data output and device lifecycle evidence")
    match result:
        case Ok(outputs):
            expect(outputs.set_a.set_id).to_equal(
                X25519MlKem768PinnedSet.MlKem)
            expect(outputs.set_b.set_id).to_equal(
                X25519MlKem768PinnedSet.X25519)
            expect(outputs.set_c.set_id).to_equal(
                X25519MlKem768PinnedSet.Hybrid)
            expect(outputs.selected_backend).to_equal(
                X25519MlKem768Backend.Vulkan)
            expect(outputs.artifact_digest).to_equal(
                "13ef51351c0147cf5fc71877d4eaac6730796e6833d78b49126e3159936d11e6")
            expect(outputs.execution_proof_digest).to_equal(
                outputs.artifact_digest)
            expect(outputs.candidate_oracle_match).to_be(true)
            expect(outputs.fallback_used).to_be(false)
            expect(outputs.accelerated_operation_count).to_equal(3)
            expect(outputs.kernel_invocations).to_equal(7)
            expect(outputs.compiled).to_be(true)
            expect(outputs.submitted).to_be(true)
            expect(outputs.fence_completed).to_be(true)
            expect(outputs.device_readback).to_be(true)
            expect(executor.session.generation).to_equal(1)
            expect(executor.zeta_encoding_count).to_equal(1)
            step("Reject the adjacent invalid operation without stale fence state")
            match x25519_mlkem768_vulkan_ntt_execute(executor, []):
                case Ok(_): fail("Vulkan accepted an empty post-success batch")
                case Err(reason): expect(reason).to_equal(
                    "vulkan-ntt-input-size-invalid")
            expect(executor.fence_completed).to_be(false)
        case Err(reason): fail(reason)
```

</details>

#### should keep unverified GPU resolvers from claiming scalar parity for REQ-010

- Resolve CUDA, Metal, and Vulkan candidates before oracle comparison
-  vulkan candidate config
-  vulkan candidate config
-  vulkan candidate config


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve CUDA, Metal, and Vulkan candidates before oracle comparison")
match x25519_mlkem768_resolve_cuda_candidate(
        _vulkan_candidate_config(X25519MlKem768Backend.Cuda), "keygen"):
    case Ok(evidence): expect(evidence.oracle_match).to_be(false)
    case Err(reason): fail(reason)
match x25519_mlkem768_resolve_metal_candidate(
        _vulkan_candidate_config(X25519MlKem768Backend.Metal), "keygen"):
    case Ok(evidence): expect(evidence.oracle_match).to_be(false)
    case Err(reason): fail(reason)
match x25519_mlkem768_resolve_vulkan_candidate(
        _vulkan_candidate_config(X25519MlKem768Backend.Vulkan), "keygen"):
    case Ok(evidence): expect(evidence.oracle_match).to_be(false)
    case Err(reason): fail(reason)
```

</details>

#### should validate and fail closed across all three operations for REQ-010

- Exercise invalid inputs and missing SPIR-V across the full facade
- config, missing, x25519 mlkem768 fixture bytes32
- x25519 mlkem768 fixture list32
- config, missing, [], x25519 mlkem768 fixture bytes32
- x25519 mlkem768 fixture list32
- config, missing, [], x25519 mlkem768 fixture bytes32
- config, missing, x25519 mlkem768 fixture bytes32
- x25519 mlkem768 fixture list32
- x25519 mlkem768 fixture list32
- config, missing,  vulkan zero list
- x25519 mlkem768 fixture bytes32
- x25519 mlkem768 fixture list32
- config, missing,  vulkan zero list
- x25519 mlkem768 fixture bytes32
-  vulkan zero list
- missing shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise invalid inputs and missing SPIR-V across the full facade")
val config = _vulkan_candidate_config(X25519MlKem768Backend.Vulkan)
var missing = X25519MlKem768VulkanNttExecutor.create_binaries(
    "test/fixtures/crypto/x25519mlkem768/missing.spv",
    "0123456789abcdef",
    "test/fixtures/crypto/x25519mlkem768/missing_inverse.spv",
    "fedcba9876543210")
match x25519_mlkem768_keygen_vulkan_candidate(
        config, missing, x25519_mlkem768_fixture_bytes32(1), [],
        x25519_mlkem768_fixture_list32(65)):
    case Ok(_): fail("Vulkan keygen accepted an invalid seed")
    case Err(reason): expect(reason).to_contain("three 32-byte inputs")
match x25519_mlkem768_encapsulate_vulkan_candidate(
        config, missing, [], x25519_mlkem768_fixture_bytes32(97),
        x25519_mlkem768_fixture_list32(129)):
    case Ok(_): fail("Vulkan encapsulation accepted an invalid share")
    case Err(reason): expect(reason).to_contain("1216 bytes")
match x25519_mlkem768_decapsulate_vulkan_candidate(
        config, missing, [], x25519_mlkem768_fixture_bytes32(1), []):
    case Ok(_): fail("Vulkan decapsulation accepted an invalid share")
    case Err(reason): expect(reason).to_contain("1120 bytes")
match x25519_mlkem768_keygen_vulkan_candidate(
        config, missing, x25519_mlkem768_fixture_bytes32(1),
        x25519_mlkem768_fixture_list32(33),
        x25519_mlkem768_fixture_list32(65)):
    case Ok(_): fail("Vulkan keygen ran without admitted SPIR-V")
    case Err(reason): expect(reason).to_contain("vulkan-ntt-binary")
match x25519_mlkem768_encapsulate_vulkan_candidate(
        config, missing, _vulkan_zero_list(1216),
        x25519_mlkem768_fixture_bytes32(97),
        x25519_mlkem768_fixture_list32(129)):
    case Ok(_): fail("Vulkan encapsulation ran without admitted SPIR-V")
    case Err(reason): expect(reason).to_contain("vulkan-ntt-binary")
match x25519_mlkem768_decapsulate_vulkan_candidate(
        config, missing, _vulkan_zero_list(1120),
        x25519_mlkem768_fixture_bytes32(1),
        _vulkan_zero_list(2400)):
    case Ok(_): fail("Vulkan decapsulation ran without admitted SPIR-V")
    case Err(reason): expect(reason).to_contain("vulkan-ntt-binary")
missing.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/crypto/x25519mlkem768_vulkan_candidate_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 Vulkan full candidate facade.
- X25519MLKEM768 Vulkan full candidate facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
