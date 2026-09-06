# X25519mlkem768 Simd Operation Evidence Specification

> Tests covering X25519MLKEM768 SIMD operation evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Simd Operation Evidence Specification

## Scenarios

### X25519MLKEM768 SIMD operation evidence

#### should reject an operation with no native SIMD chunks

- Submit an AVX2 receipt whose native chunk count is zero
-  evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit an AVX2 receipt whose native chunk count is zero")
match x25519_mlkem768_simd_operation_evidence(
        _evidence(X25519MlKem768Backend.Avx2), _receipt(1, 0, 0)):
    case Ok(_): fail("zero-hit SIMD evidence was accepted")
    case Err(reason): expect(reason).to_contain("no native execution receipt")
```

</details>

#### should reject unknown and mismatched SIMD backends

- Reject a receipt code outside the AVX2, NEON, and RVV registry
-  evidence
- Reject a NEON receipt for an AVX2-admitted operation
-  evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a receipt code outside the AVX2, NEON, and RVV registry")
match x25519_mlkem768_simd_operation_evidence(
        _evidence(X25519MlKem768Backend.Avx2), _receipt(4, 1, 0)):
    case Ok(_): fail("unknown SIMD backend was accepted")
    case Err(reason): expect(reason).to_contain("unknown backend")

step("Reject a NEON receipt for an AVX2-admitted operation")
match x25519_mlkem768_simd_operation_evidence(
        _evidence(X25519MlKem768Backend.Avx2), _receipt(2, 1, 0)):
    case Ok(_): fail("mismatched SIMD backend was accepted")
    case Err(reason): expect(reason).to_contain("does not match")
```

</details>

#### should reject impossible RVV VLEN metadata

- Reject an RVV vector length below the architectural minimum
-  evidence
- Reject an RVV vector length that is not a 32-bit multiple
-  evidence
- Reject RVV-only metadata on an adjacent NEON receipt
-  evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject an RVV vector length below the architectural minimum")
match x25519_mlkem768_simd_operation_evidence(
        _evidence(X25519MlKem768Backend.Rvv), _receipt(3, 1, 96)):
    case Ok(_): fail("short RVV VLEN was accepted")
    case Err(reason): expect(reason).to_contain("invalid RVV VLEN")

step("Reject an RVV vector length that is not a 32-bit multiple")
match x25519_mlkem768_simd_operation_evidence(
        _evidence(X25519MlKem768Backend.Rvv), _receipt(3, 1, 130)):
    case Ok(_): fail("misaligned RVV VLEN was accepted")
    case Err(reason): expect(reason).to_contain("invalid RVV VLEN")

step("Reject RVV-only metadata on an adjacent NEON receipt")
match x25519_mlkem768_simd_operation_evidence(
        _evidence(X25519MlKem768Backend.Neon), _receipt(2, 1, 128)):
    case Ok(_): fail("RVV metadata on NEON was accepted")
    case Err(reason): expect(reason).to_contain("non-RVV receipt")
```

</details>

#### should promote AVX2, NEON, and RVV receipts with provenance

- Promote valid receipts at the AVX2, NEON, and RVV boundary
-
-
-
   - Expected: updated.selected_backend equals `evidence.requested_backend`
   - Expected: updated.simd_chunk_hits equals `receipt.chunk_hits`
   - Expected: updated.execution_proof_digest equals `"a" * 64`
   - Expected: updated.kernel_invocations equals `0`
   - Expected: updated.compiled is false
   - Expected: updated.submitted is false
   - Expected: updated.fence_completed is false
   - Expected: updated.device_readback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Promote valid receipts at the AVX2, NEON, and RVV boundary")
val cases = [
    (_evidence(X25519MlKem768Backend.Avx2), _receipt(1, 2, 0)),
    (_evidence(X25519MlKem768Backend.Neon), _receipt(2, 3, 0)),
    (_evidence(X25519MlKem768Backend.Rvv), _receipt(3, 4, 128))]
for (evidence, receipt) in cases:
    match x25519_mlkem768_simd_operation_evidence(evidence, receipt):
        case Err(reason): fail(reason)
        case Ok(updated):
            expect(updated.selected_backend).to_equal(evidence.requested_backend)
            expect(updated.simd_chunk_hits).to_equal(receipt.chunk_hits)
            expect(updated.observed_rvv_vlen_bits).to_equal(
                receipt.observed_rvv_vlen_bits)
            expect(updated.execution_proof_digest).to_equal("a" * 64)
            expect(updated.kernel_invocations).to_equal(0)
            expect(updated.compiled).to_equal(false)
            expect(updated.submitted).to_equal(false)
            expect(updated.fence_completed).to_equal(false)
            expect(updated.device_readback).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_simd_operation_evidence_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 SIMD operation evidence.
- X25519MLKEM768 SIMD operation evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
