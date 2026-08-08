# X25519mlkem768 Gpu Scalar Verification Specification

> Tests covering X25519MLKEM768 GPU scalar differential verification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Gpu Scalar Verification Specification

## Scenarios

### X25519MLKEM768 GPU scalar differential verification

#### should expose no caller-controlled scalar verification bypass

- Inspect the hybrid module's complete public candidate surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the hybrid module's complete public candidate surface")
val source = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(source.contains(
    "export x25519_mlkem768_keygen_qualified_simd_measurement_candidate"
    )).to_be(false)
expect(source.contains(
    "export x25519_mlkem768_keygen_qualified_cuda_measurement_candidate"
    )).to_be(false)
expect(source.contains(
    "export x25519_mlkem768_keygen_qualified_vulkan_measurement_candidate"
    )).to_be(false)
expect(source).to_contain(
    "config, executor, x25519_private, d, z, true)")
expect(source).to_contain(
    "config, admission, x25519_private, d, z, true)")
```

</details>

#### should accept the exact scalar keygen encapsulation and decapsulation outputs

- Generate one deterministic ML-KEM fixture for every GPU verifier
   - Expected: x25519_mlkem768_verify_gpu_keygen(seed, seed, ek, dk) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate one deterministic ML-KEM fixture for every GPU verifier")
val (seed, ek, dk, shared, ciphertext, recovered) = _valid_material()
expect(x25519_mlkem768_verify_gpu_keygen(seed, seed, ek, dk)).to_equal("")
expect(x25519_mlkem768_verify_gpu_encapsulate(
    ek, seed, shared, ciphertext)).to_equal("")
expect(x25519_mlkem768_verify_gpu_decapsulate(
    dk, ciphertext, recovered)).to_equal("")
```

</details>

#### should reject every independently corrupted GPU public output

- Corrupt each key-generation output without skipping its paired comparison
- Corrupt each encapsulation output independently
- Corrupt the decapsulated shared secret


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Corrupt each key-generation output without skipping its paired comparison")
val (seed, ek, dk, shared, ciphertext, recovered) = _valid_material()
expect(x25519_mlkem768_verify_gpu_keygen(
    seed, seed, _changed(ek, 0), dk)).to_equal(
        "GPU key generation failed scalar verification")
expect(x25519_mlkem768_verify_gpu_keygen(
    seed, seed, ek, _changed(dk, dk.len() - 1))).to_equal(
        "GPU key generation failed scalar verification")

step("Corrupt each encapsulation output independently")
expect(x25519_mlkem768_verify_gpu_encapsulate(
    ek, seed, _changed(shared, 0), ciphertext)).to_equal(
        "GPU encapsulation failed scalar verification")
expect(x25519_mlkem768_verify_gpu_encapsulate(
    ek, seed, shared, _changed(ciphertext, ciphertext.len() - 1))).to_equal(
        "GPU encapsulation failed scalar verification")

step("Corrupt the decapsulated shared secret")
expect(x25519_mlkem768_verify_gpu_decapsulate(
    dk, ciphertext, _changed(recovered, 0))).to_equal(
        "GPU decapsulation failed scalar verification")
```

</details>

#### should preserve checked ML-KEM failures at every scalar verifier boundary

- Reject invalid key-generation seed material
- Reject an invalid encapsulation key before output comparison
- Reject an invalid decapsulation key before output comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject invalid key-generation seed material")
val (seed, ek, dk, shared, ciphertext, _) = _valid_material()
expect(x25519_mlkem768_verify_gpu_keygen([], seed, ek, dk)).to_contain(
    "scalar key generation verification failed")

step("Reject an invalid encapsulation key before output comparison")
expect(x25519_mlkem768_verify_gpu_encapsulate(
    [], seed, shared, ciphertext)).to_contain(
        "scalar encapsulation verification failed")

step("Reject an invalid decapsulation key before output comparison")
expect(x25519_mlkem768_verify_gpu_decapsulate(
    [], ciphertext, shared)).to_contain(
        "scalar decapsulation verification failed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 GPU scalar differential verification.
- X25519MLKEM768 GPU scalar differential verification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
