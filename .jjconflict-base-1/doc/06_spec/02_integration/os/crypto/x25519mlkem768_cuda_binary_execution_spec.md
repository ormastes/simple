# X25519mlkem768 Cuda Binary Execution Specification

> Tests covering X25519MLKEM768 pure-Simple exact CUDA binary execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Cuda Binary Execution Specification

## Scenarios

### X25519MLKEM768 pure-Simple exact CUDA binary execution

#### should load admitted sm86 cubin bytes and execute both NTT entries

- Verify cubin provenance and execute forward and inverse NTT
   - Expected: retained_digest equals `_SM86_CUBIN_SHA256`
- sha256 u8 hex
   - Expected: admitted_byte_count equals `retained_byte_count`
   - Expected: admitted_digest equals `_SM86_CUBIN_SHA256`
   - Expected: source_digest equals ``
   - Expected: forward.kernel_invocations equals `1`
   - Expected: forward.artifact_digest equals `_SM86_CUBIN_SHA256`
   - Expected: inverse.device_identity equals `forward.device_identity`
   - Expected: inverse.kernel_invocations equals `1`
   - Expected: inverse.artifact_digest equals `_SM86_CUBIN_SHA256`
- executor shutdown
   - Expected: generation equals `1`
   - Expected: invocation_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify cubin provenance and execute forward and inverse NTT")
val host_available = cuda_available()
expect(host_available).to_be(true)

val retained_digest = file_hash_sha256(_SM86_CUBIN_PATH)
val retained_byte_count = file_size(_SM86_CUBIN_PATH)
expect(retained_digest).to_equal(_SM86_CUBIN_SHA256)
expect(retained_byte_count).to_be_greater_than(0)

val fixture = x25519_mlkem768_ntt_fixture(1)
val expected_forward = ntt(fixture)
val expected_inverse = intt(expected_forward)
var executor = X25519MlKem768CudaNttExecutor.create_binary(
    _SM86_CUBIN_PATH, _SM86_CUBIN_SHA256)
val admitted_byte_count = executor.artifact_bytes.len()
val independently_hashed_admitted_bytes =
    sha256_u8_hex(executor.artifact_bytes)
val admitted_digest = executor.artifact_digest
val binary_mode = executor.use_binary
val source_digest = executor.source_digest
expect(admitted_byte_count).to_equal(retained_byte_count)
expect(independently_hashed_admitted_bytes).to_equal(
    _SM86_CUBIN_SHA256)
expect(admitted_digest).to_equal(_SM86_CUBIN_SHA256)
expect(binary_mode).to_be(true)
expect(source_digest).to_equal("")

val forward = x25519_mlkem768_cuda_ntt_execute(executor, fixture)
expect(forward.completed).to_be(true)
expect(forward.compiled).to_be(true)
expect(forward.submitted).to_be(true)
expect(forward.fence_completed).to_be(true)
expect(forward.device_readback).to_be(true)
expect(forward.device_identity).to_be_greater_than(0)
expect(forward.kernel_invocations).to_equal(1)
expect(forward.artifact_digest).to_equal(_SM86_CUBIN_SHA256)
expect(_cuda_binary_lists_equal(
    forward.values, expected_forward)).to_be(true)

val inverse = x25519_mlkem768_cuda_intt_execute(
    executor, forward.values)
expect(inverse.completed).to_be(true)
expect(inverse.compiled).to_be(true)
expect(inverse.submitted).to_be(true)
expect(inverse.fence_completed).to_be(true)
expect(inverse.device_readback).to_be(true)
expect(inverse.device_identity).to_equal(forward.device_identity)
expect(inverse.kernel_invocations).to_equal(1)
expect(inverse.artifact_digest).to_equal(_SM86_CUBIN_SHA256)
expect(_cuda_binary_lists_equal(
    inverse.values, expected_inverse)).to_be(true)

val module_loaded = executor.session.module > 0
val generation = executor.session.generation
val invocation_count = executor.kernel_invocations
executor.shutdown()

expect(module_loaded).to_be(true)
expect(generation).to_equal(1)
expect(invocation_count).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 pure-Simple exact CUDA binary execution.
- X25519MLKEM768 pure-Simple exact CUDA binary execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
