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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose no caller-controlled scalar verification bypass
- Inspect the hybrid module's complete public candidate surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should expose no caller-controlled scalar verification bypass")
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

- should accept the exact scalar keygen encapsulation and decapsulation outputs
- Generate one deterministic ML-KEM fixture for every GPU verifier
   - Expected: x25519_mlkem768_verify_gpu_keygen(seed, seed, ek, dk) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should accept the exact scalar keygen encapsulation and decapsulation outputs")
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

- should reject every independently corrupted GPU public output
- Corrupt each key-generation output without skipping its paired comparison
- Corrupt each encapsulation output independently
- Corrupt the decapsulated shared secret


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject every independently corrupted GPU public output")
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

- should preserve checked ML-KEM failures at every scalar verifier boundary
- Reject invalid key-generation seed material
- Reject an invalid encapsulation key before output comparison
- Reject an invalid decapsulation key before output comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should preserve checked ML-KEM failures at every scalar verifier boundary")
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
| Updated | 2026-08-26 |
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `340cfe39116d23cc65c9998859e24e5a4c8a744630ee391c9adf65b6fcc0dddb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `340cfe39116d23cc65c9998859e24e5a4c8a744630ee391c9adf65b6fcc0dddb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `340cfe39116d23cc65c9998859e24e5a4c8a744630ee391c9adf65b6fcc0dddb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=80 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose no caller-controlled scalar verification bypass' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose no caller-controlled scalar verification bypass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept the exact scalar keygen encapsulation and decapsulation outputs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept the exact scalar keygen encapsulation and decapsulation outputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject every independently corrupted GPU public output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject every independently corrupted GPU public output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_gpu_scalar_verification_spec.spl:111:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve checked ML-KEM failures at every scalar verifier boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
