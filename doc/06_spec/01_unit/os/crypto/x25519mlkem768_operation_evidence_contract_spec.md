# X25519mlkem768 Operation Evidence Contract Specification

> Tests covering X25519MLKEM768 extracted operation evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Operation Evidence Contract Specification

## Scenarios

### X25519MLKEM768 extracted operation evidence

#### should keep every extracted module below 800 lines

- Count the GPU, SIMD, and hybrid module lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Count the GPU, SIMD, and hybrid module lines")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
val simd = file_read_text(
    "src/os/crypto/x25519_mlkem768/simd_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(gpu.split("\n").len()).to_be_less_than(800)
expect(simd.split("\n").len()).to_be_less_than(800)
expect(hybrid.split("\n").len()).to_be_less_than(800)
```

</details>

#### should map all three GPU providers through all three scalar checks

- Count keygen, encapsulation, and decapsulation verifier calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Count keygen, encapsulation, and decapsulation verifier calls")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
val implementation = gpu + hybrid
expect(implementation.split(
    "x25519_mlkem768_verify_gpu_keygen(").len()).to_equal(5)
expect(implementation.split(
    "x25519_mlkem768_verify_gpu_encapsulate(").len()).to_equal(5)
expect(implementation.split(
    "x25519_mlkem768_verify_gpu_decapsulate(").len()).to_equal(5)
```

</details>

#### should compare paired secret-bearing results before branching

- Inspect constant-work scalar differential comparisons
- "var difference: i64 = left len


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect constant-work scalar differential comparisons")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
expect(gpu).to_contain("val encapsulation_key_matches =")
expect(gpu).to_contain("val decapsulation_key_matches =")
expect(gpu).to_contain("val shared_matches =")
expect(gpu).to_contain("val ciphertext_matches =")
expect(gpu).to_contain(
    "var difference: i64 = left.len() ^ right.len()")
expect(gpu.contains(
    "if left.len() != right.len()")).to_equal(false)
expect(gpu.contains(
    "if (not _gpu_lists_equal(encapsulation_key")).to_equal(false)
expect(gpu.contains(
    "if (not _gpu_lists_equal(mlkem_shared")).to_equal(false)
```

</details>

#### should fail closed without a current GPU lifecycle receipt

- Inspect invocation and readback gates before evidence promotion
   - Expected: gpu.split("operation_invocations < 1").len() equals `4`
   - Expected: gpu.split(baseline_guard).len() equals `4`
   - Expected: gpu.split("if not executor.fence_completed").len() equals `4`
   - Expected: gpu.split("updated.device_readback = true").len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect invocation and readback gates before evidence promotion")
val gpu = file_read_text(
    "src/os/crypto/x25519_mlkem768/gpu_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(gpu.split("operation_invocations < 1").len()).to_equal(4)
val baseline_guard =
    "invocations_before < 0 or executor.kernel_invocations < invocations_before"
expect(gpu.split(baseline_guard).len()).to_equal(4)
expect(gpu.split("if not executor.fence_completed").len()).to_equal(4)
expect(gpu.split("updated.device_readback = true").len()).to_equal(4)
expect(hybrid.split(
    "match x25519_mlkem768_cuda_operation_evidence(").len()).to_equal(4)
expect(hybrid.split(
    "match x25519_mlkem768_metal_operation_evidence(").len()).to_equal(4)
expect(hybrid.split(
    "match x25519_mlkem768_vulkan_operation_evidence(").len()).to_equal(4)
```

</details>

#### should retain admitted SIMD artifact provenance as execution proof

- Separate runtime provenance proof from the public output digest
- "evidence execution proof digest = evidence output digest") len
   - Expected: scalar_proof_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Separate runtime provenance proof from the public output digest")
val simd = file_read_text(
    "src/os/crypto/x25519_mlkem768/simd_operation_evidence.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
expect(simd).to_contain(
    "updated.execution_proof_digest = updated.artifact_digest")
# Only the three scalar operations use their public output as proof.
val scalar_proof_count = hybrid.split(
    "evidence.execution_proof_digest = evidence.output_digest").len()
expect(scalar_proof_count).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_operation_evidence_contract_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 extracted operation evidence.
- X25519MLKEM768 extracted operation evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
