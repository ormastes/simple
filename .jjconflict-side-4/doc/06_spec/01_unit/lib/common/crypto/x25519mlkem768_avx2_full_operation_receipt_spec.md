# X25519mlkem768 Avx2 Full Operation Receipt Specification

> Tests covering X25519MLKEM768 native AVX2 full-operation receipt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Avx2 Full Operation Receipt Specification

## Scenarios

### X25519MLKEM768 native AVX2 full-operation receipt

#### emits a promotable receipt only with a matching typed performance attestation

- Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (key_pair, encapsulation, decapsulation) = _roundtrip()
val result = x25519_mlkem768_compose_avx2_full_operation_receipt(
    _binding(key_pair.evidence.output_digest,
        encapsulation.evidence.output_digest,
        decapsulation.evidence.output_digest),
    key_pair, encapsulation, decapsulation,
    Some(_performance_attestation()))
expect(result.is_ok()).to_be(true)
val receipt = result.unwrap()
expect(receipt.promotion_eligible).to_be(true)
expect(receipt.reason).to_equal(
    "native-avx2-full-operation-performance-admitted")
```

</details>

#### validates native SIMD outputs but blocks correctness-only promotion

- Validate one complete AVX2 keygen encapsulate and decapsulate result


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate one complete AVX2 keygen encapsulate and decapsulate result")
val (key_pair, encapsulation, decapsulation) = _roundtrip()
val binding = _binding(
    key_pair.evidence.output_digest,
    encapsulation.evidence.output_digest,
    decapsulation.evidence.output_digest)
val result = x25519_mlkem768_compose_avx2_full_operation_receipt(
    binding, key_pair, encapsulation, decapsulation)
expect(result.is_err()).to_be(true)
expect(result.unwrap_err()).to_equal(
    "avx2-performance-attestation-missing")
```

</details>

#### rejects a scalar fallback disguised as AVX2 evidence

- Tamper one selected backend before receipt composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Tamper one selected backend before receipt composition")
val (key_pair, encapsulation, decapsulation) = _roundtrip()
var tampered = encapsulation
tampered.evidence.selected_backend = X25519MlKem768Backend.ScalarCpu
val result = x25519_mlkem768_compose_avx2_full_operation_receipt(
    _binding(key_pair.evidence.output_digest,
        encapsulation.evidence.output_digest,
        decapsulation.evidence.output_digest),
    key_pair, tampered, decapsulation)
expect(result.is_err()).to_be(true)
```

</details>

#### rejects mismatched compiler artifacts and absolute outputs

- Bind a different Stage-4 binary than the operation executed
- Bind an absolute-oracle digest for different public output


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind a different Stage-4 binary than the operation executed")
val (key_pair, encapsulation, decapsulation) = _roundtrip()
var wrong_binary = _binding(
    key_pair.evidence.output_digest,
    encapsulation.evidence.output_digest,
    decapsulation.evidence.output_digest)
wrong_binary.stage4_binary_sha256 = "f" * 64
val artifact_result = x25519_mlkem768_compose_avx2_full_operation_receipt(
    wrong_binary, key_pair, encapsulation, decapsulation)
expect(artifact_result.is_err()).to_be(true)

step("Bind an absolute-oracle digest for different public output")
var wrong_oracle = _binding(
    key_pair.evidence.output_digest,
    encapsulation.evidence.output_digest,
    decapsulation.evidence.output_digest)
wrong_oracle.expected_decapsulate_digest = "0" * 64
val oracle_result = x25519_mlkem768_compose_avx2_full_operation_receipt(
    wrong_oracle, key_pair, encapsulation, decapsulation)
expect(oracle_result.is_err()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 native AVX2 full-operation receipt.
- X25519MLKEM768 native AVX2 full-operation receipt

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
