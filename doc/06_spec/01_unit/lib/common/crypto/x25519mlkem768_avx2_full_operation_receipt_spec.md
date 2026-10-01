# X25519mlkem768 Avx2 Full Operation Receipt Specification

> Tests covering X25519MLKEM768 native AVX2 full-operation receipt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Avx2 Full Operation Receipt Specification

## Scenarios

### X25519MLKEM768 native AVX2 full-operation receipt

#### emits a promotable receipt only with a matching typed performance attestation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a promotable receipt only with a matching typed performance attestation


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits a promotable receipt only with a matching typed performance attestation")
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

#### fails closed when the pinned full-workload digest is empty or malformed

- fails closed when the pinned full-workload digest is empty or malformed


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed when the pinned full-workload digest is empty or malformed")
val (key_pair, encapsulation, decapsulation) = _roundtrip()
var empty = _binding(key_pair.evidence.output_digest,
    encapsulation.evidence.output_digest,
    decapsulation.evidence.output_digest)
empty.pinned_workload_sha256 = ""
expect(x25519_mlkem768_compose_avx2_full_operation_receipt(
    empty, key_pair, encapsulation, decapsulation).is_err()).to_be(true)
var malformed = _binding(key_pair.evidence.output_digest,
    encapsulation.evidence.output_digest,
    decapsulation.evidence.output_digest)
malformed.pinned_workload_sha256 = "G" * 64
expect(x25519_mlkem768_compose_avx2_full_operation_receipt(
    malformed, key_pair, encapsulation, decapsulation).is_err()).to_be(true)
```

</details>

#### validates native SIMD outputs but blocks correctness-only promotion

- validates native SIMD outputs but blocks correctness-only promotion
- Validate one complete AVX2 keygen encapsulate and decapsulate result


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates native SIMD outputs but blocks correctness-only promotion")
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

- rejects a scalar fallback disguised as AVX2 evidence
- Tamper one selected backend before receipt composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a scalar fallback disguised as AVX2 evidence")
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

- rejects mismatched compiler artifacts and absolute outputs
- Bind a different Stage-4 binary than the operation executed
- Bind an absolute-oracle digest for different public output


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects mismatched compiler artifacts and absolute outputs")
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

#### admits AVX2 NEON and RVV only as matching native Stage-4 SIMD receipts

- admits AVX2 NEON and RVV only as matching native Stage-4 SIMD receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits AVX2 NEON and RVV only as matching native Stage-4 SIMD receipts")
val backends = [X25519MlKem768EvidenceBackend.Avx2,
    X25519MlKem768EvidenceBackend.Neon, X25519MlKem768EvidenceBackend.Rvv]
var index: i64 = 0
while index < backends.len():
    val backend = backends[index]
    var vlen: i64 = 0
    if backend == X25519MlKem768EvidenceBackend.Rvv:
        vlen = 128
    val (key_pair, encapsulation, decapsulation) = _generic_roundtrip(backend, vlen)
    val result = x25519_mlkem768_compose_simd_full_operation_receipt(
        _simd_binding(backend, key_pair.evidence.output_digest,
            encapsulation.evidence.output_digest, decapsulation.evidence.output_digest),
        key_pair, encapsulation, decapsulation, Some(_generic_performance(backend)))
    expect(result.is_ok()).to_be(true)
    index = index + 1
```

</details>

#### rejects missing SIMD hits and an RVV VLEN below the binding minimum

- rejects missing SIMD hits and an RVV VLEN below the binding minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing SIMD hits and an RVV VLEN below the binding minimum")
val (key_pair, encapsulation, decapsulation) = _generic_roundtrip(
    X25519MlKem768EvidenceBackend.Neon, 0)
var no_hits = encapsulation
no_hits.evidence.simd_chunk_hits = 0
expect(x25519_mlkem768_compose_simd_full_operation_receipt(
    _simd_binding(X25519MlKem768EvidenceBackend.Neon,
        key_pair.evidence.output_digest, encapsulation.evidence.output_digest,
        decapsulation.evidence.output_digest), key_pair, no_hits, decapsulation,
    Some(_generic_performance(X25519MlKem768EvidenceBackend.Neon))).is_err()).to_be(true)
val (rvv_key, rvv_encapsulation, rvv_decapsulation) = _generic_roundtrip(
    X25519MlKem768EvidenceBackend.Rvv, 64)
expect(x25519_mlkem768_compose_simd_full_operation_receipt(
    _simd_binding(X25519MlKem768EvidenceBackend.Rvv,
        rvv_key.evidence.output_digest, rvv_encapsulation.evidence.output_digest,
        rvv_decapsulation.evidence.output_digest), rvv_key, rvv_encapsulation,
    rvv_decapsulation, Some(_generic_performance(X25519MlKem768EvidenceBackend.Rvv))).is_err()).to_be(true)
```

</details>

#### rejects a SIMD receipt whose host architecture cannot execute its backend

- rejects a SIMD receipt whose host architecture cannot execute its backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a SIMD receipt whose host architecture cannot execute its backend")
val (key_pair, encapsulation, decapsulation) = _generic_roundtrip(
    X25519MlKem768EvidenceBackend.Neon, 0)
var wrong_arch = _simd_binding(X25519MlKem768EvidenceBackend.Neon,
    key_pair.evidence.output_digest, encapsulation.evidence.output_digest,
    decapsulation.evidence.output_digest)
wrong_arch.host_arch = "x86_64"
expect(x25519_mlkem768_compose_simd_full_operation_receipt(
    wrong_arch, key_pair, encapsulation, decapsulation,
    Some(_generic_performance(X25519MlKem768EvidenceBackend.Neon))).is_err()).to_be(true)
```

</details>

#### promotes only a public native SIMD observation with admitted performance

- promotes only a public native SIMD observation with admitted performance
   - Expected: receipt.keygen_output_digest equals `sha256_text(keygen)`
   - Expected: receipt.encapsulate_output_digest equals `sha256_text(encapsulate)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("promotes only a public native SIMD observation with admitted performance")
val keygen = "4" * 64
val encapsulate = "5" * 64
val observation = _observation(X25519MlKem768EvidenceBackend.Avx2,
    keygen, encapsulate, encapsulate, 0)
val result = x25519_mlkem768_compose_simd_observed_full_operation_receipt(
    _simd_binding(X25519MlKem768EvidenceBackend.Avx2,
        keygen, encapsulate, encapsulate), observation,
    Some(_generic_performance(X25519MlKem768EvidenceBackend.Avx2)))
expect(result.is_ok()).to_be(true)
val receipt = result.unwrap()
expect(receipt.promotion_eligible).to_be(true)
expect(receipt.keygen_output_digest).to_equal(sha256_text(keygen))
expect(receipt.encapsulate_output_digest).to_equal(sha256_text(encapsulate))
```

</details>

#### rejects a raw SIMD observation that falsely claims promotion

- rejects a raw SIMD observation that falsely claims promotion


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a raw SIMD observation that falsely claims promotion")
val keygen = "4" * 64
val encapsulate = "5" * 64
var observation = _observation(X25519MlKem768EvidenceBackend.Avx2,
    keygen, encapsulate, encapsulate, 0)
observation.raw_receipt.promotion_eligible = true
expect(x25519_mlkem768_compose_simd_observed_full_operation_receipt(
    _simd_binding(X25519MlKem768EvidenceBackend.Avx2,
        keygen, encapsulate, encapsulate), observation,
    Some(_generic_performance(X25519MlKem768EvidenceBackend.Avx2))).is_err()).to_be(true)
```

</details>

#### rejects tampered public operation outputs before promotion

- rejects tampered public operation outputs before promotion


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects tampered public operation outputs before promotion")
val keygen = "4" * 64
val encapsulate = "5" * 64
var observation = _observation(X25519MlKem768EvidenceBackend.Avx2,
    keygen, encapsulate, encapsulate, 0)
observation.raw_receipt.decapsulate_output_digest = "6" * 64
expect(x25519_mlkem768_compose_simd_observed_full_operation_receipt(
    _simd_binding(X25519MlKem768EvidenceBackend.Avx2,
        keygen, encapsulate, encapsulate), observation,
    Some(_generic_performance(X25519MlKem768EvidenceBackend.Avx2))).is_err()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 native AVX2 full-operation receipt.
- X25519MLKEM768 native AVX2 full-operation receipt

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4e7a9d9c00c61e04ddec7699ad4de5014b240f746faf40429aacb0742d23e50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4e7a9d9c00c61e04ddec7699ad4de5014b240f746faf40429aacb0742d23e50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4e7a9d9c00c61e04ddec7699ad4de5014b240f746faf40429aacb0742d23e50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.spl:314:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a promotable receipt only with a matching typed performance attestation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.spl:330:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when the pinned full-workload digest is empty or malformed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_avx2_full_operation_receipt_spec.spl:347:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates native SIMD outputs but blocks correctness-only promotion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
