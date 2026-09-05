# X25519mlkem768 Simd Provenance Contract Specification

> Tests covering X25519MLKEM768 SIMD source provenance contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Simd Provenance Contract Specification

## Scenarios

### X25519MLKEM768 SIMD source provenance contract

#### should bind AVX2 NEON and RVV evidence to the admitted Stage-4 build (NFR-012)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should bind AVX2 NEON and RVV evidence to the admitted Stage-4 build (NFR-012)
- Compare every ISA record with the build source and binary digests
   - Expected: pair[0] equals `_SOURCE_REVISION`
   - Expected: pair[1] equals `_BINARY_DIGEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should bind AVX2 NEON and RVV evidence to the admitted Stage-4 build (NFR-012)")
step("Compare every ISA record with the build source and binary digests")
for pair in [
        _simd_evidence_digests(X25519MlKem768Backend.Avx2, 1),
        _simd_evidence_digests(X25519MlKem768Backend.Neon, 2),
        _simd_evidence_digests(X25519MlKem768Backend.Rvv, 3)]:
    expect(pair[0]).to_equal(_SOURCE_REVISION)
    expect(pair[1]).to_equal(_BINARY_DIGEST)
```

</details>

#### should reject implicit or mismatched build provenance (NFR-012)

- should reject implicit or mismatched build provenance (NFR-012)
- Require an admitted sidecar bound to the actual running binary
- Reject ambiguous provenance with a duplicated source-roots key


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should reject implicit or mismatched build provenance (NFR-012)")
step("Require an admitted sidecar bound to the actual running binary")
val implicit = match x25519_mlkem768_resolve_simd_candidate_for_test(
        _simd_config(X25519MlKem768Backend.Avx2),
        "provenance-contract", 1):
    case Ok(_): "accepted"
    case Err(reason): reason
expect(implicit).to_equal(
    "requested SIMD candidate requires admitted Stage-4 build provenance")
val mismatched = match x25519_mlkem768_resolve_simd_candidate_with_stage4_provenance_for_test(
        _simd_config(X25519MlKem768Backend.Avx2),
        "provenance-contract", 1, _stage4_provenance(),
        _SOURCE_REVISION, _PROVENANCE_DIGEST):
    case Ok(_): "accepted"
    case Err(reason): reason
expect(mismatched).to_equal(
    "requested SIMD candidate build provenance rejected: stage4-output-sha256-mismatch")
val admitted_provenance = _stage4_provenance()
val wrong_root_provenance = admitted_provenance.replace(
    "src/compiler:src/lib:src/app:src/runtime:examples/10_tooling",
    "src/app")
val wrong_roots = match x25519_mlkem768_resolve_simd_candidate_with_stage4_provenance_for_test(
        _simd_config(X25519MlKem768Backend.Avx2),
        "provenance-contract", 1, wrong_root_provenance,
        _BINARY_DIGEST, _PROVENANCE_DIGEST):
    case Ok(_): "accepted"
    case Err(reason): reason
expect(wrong_roots).to_equal(
    "requested SIMD candidate build provenance rejected: stage4-source-roots-invalid")

step("Reject ambiguous provenance with a duplicated source-roots key")
val duplicate_root_provenance = admitted_provenance +
    "source_roots=src/compiler:src/lib:src/app:src/runtime:examples/10_tooling\n"
val duplicate_roots = match x25519_mlkem768_resolve_simd_candidate_with_stage4_provenance_for_test(
        _simd_config(X25519MlKem768Backend.Avx2),
        "provenance-contract", 1, duplicate_root_provenance,
        _BINARY_DIGEST, _PROVENANCE_DIGEST):
    case Ok(_): "accepted"
    case Err(reason): reason
expect(duplicate_roots).to_equal(
    "requested SIMD candidate build provenance rejected: stage4-source-roots-invalid")
```

</details>

#### should validate Vulkan candidate configuration before backend admission (NFR-012)

- should validate Vulkan candidate configuration before backend admission (NFR-012)
- Reject a zero-batch Vulkan configuration at the shared policy gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should validate Vulkan candidate configuration before backend admission (NFR-012)")
step("Reject a zero-batch Vulkan configuration at the shared policy gate")
val invalid = X25519MlKem768Config(
    implementation_version: X25519_MLKEM768_IMPLEMENTATION_VERSION,
    profile_version: X25519_MLKEM768_PROFILE_VERSION,
    requested_backend: X25519MlKem768Backend.Vulkan,
    selection_mode: X25519MlKem768SelectionMode.Require,
    verification_policy:
        X25519MlKem768VerificationPolicy.AbsoluteAndScalar,
    minimum_batch: 1,
    batch_size: 0)
match x25519_mlkem768_resolve_vulkan_candidate(invalid, "keygen"):
    case Ok(_): fail("invalid Vulkan configuration was accepted")
    case Err(reason): expect(reason).to_contain("batch_size must be positive")
```

</details>

#### should keep source verification out of the operation hot path (NFR-012)

- should keep source verification out of the operation hot path (NFR-012)
- Inspect SIMD operation modules for filesystem hashing calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should keep source verification out of the operation hot path (NFR-012)")
step("Inspect SIMD operation modules for filesystem hashing calls")
val policy = file_read_text(
    "src/os/crypto/x25519_mlkem768/execution_policy.spl")
expect(policy.contains("file_hash_sha256")).to_be(false)
expect(policy.contains("file_read_text")).to_be(false)
expect(policy.contains("rt_process_run")).to_be(false)
expect(policy.contains("process_run(")).to_be(false)
expect(policy.contains(
    "b4aee39c491c3aba19b48efe3c30c723128533a85e30f3fb4361fc46e2bf47c5"
)).to_be(false)
```

</details>

#### should include the SIMD runtime in pure-Simple native builds (NFR-012)

- should include the SIMD runtime in pure-Simple native builds (NFR-012)
- Inspect the native runtime compiler source and object lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should include the SIMD runtime in pure-Simple native builds (NFR-012)")
step("Inspect the native runtime compiler source and object lists")
val compiler = file_read_text(
    "src/compiler/70.backend/backend/runtime_compiler.spl")
expect(compiler).to_contain("runtime_simd_dispatch")
expect(compiler).to_contain(
    "{" + "rt_dir" + "}/{" + "name" + "}.c")
expect(compiler).to_contain("comp_args.push(src_path)")
val stage4 = file_read_text(
    "scripts/check/lib/stage4-candidate-provenance.shs")
expect(stage4).to_contain(
    "source_roots=src/compiler:src/lib:src/app:src/runtime:" +
    "examples/10_tooling")
```

</details>

#### should require admission and report the observed SIMD path without GPU claims (NFR-012)

- should require admission and report the observed SIMD path without GPU claims (NFR-012)
- Inspect the public SIMD operation boundary and receipt mapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should require admission and report the observed SIMD path without GPU claims (NFR-012)")
step("Inspect the public SIMD operation boundary and receipt mapping")
val contract = file_read_text(
    "src/lib/common/crypto/x25519_mlkem768/contract.spl")
val hybrid = file_read_text(
    "src/os/crypto/x25519_mlkem768/hybrid.spl")
val simd_evidence = file_read_text(
    "src/os/crypto/x25519_mlkem768/simd_operation_evidence.spl")
expect(contract).to_contain("struct X25519MlKem768SimdAdmission:")
expect(contract).to_contain("simd_chunk_hits: i64")
expect(contract).to_contain("observed_rvv_vlen_bits: i64")
expect(hybrid).to_contain(
    "admission: X25519MlKem768SimdAdmission")
expect(hybrid).to_contain("mlkem_ntt_simd_receipt()")
expect(hybrid).to_contain(
    "x25519_mlkem768_simd_operation_evidence(")
expect(simd_evidence).to_contain(
    "updated.simd_chunk_hits = receipt.chunk_hits")
expect(simd_evidence).to_contain(
    "updated.observed_rvv_vlen_bits = receipt.observed_rvv_vlen_bits")
expect(simd_evidence).to_contain("updated.kernel_invocations = 0")
expect(simd_evidence).to_contain("updated.compiled = false")
expect(simd_evidence).to_contain("updated.submitted = false")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 SIMD source provenance contract.
- X25519MLKEM768 SIMD source provenance contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `6bbaf582f0972cfd7d33fc1f1b1c19a6e3ed6c42104fc5b459dd503fd24367c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bbaf582f0972cfd7d33fc1f1b1c19a6e3ed6c42104fc5b459dd503fd24367c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bbaf582f0972cfd7d33fc1f1b1c19a6e3ed6c42104fc5b459dd503fd24367c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind AVX2 NEON and RVV evidence to the admitted Stage-4 build (NFR-012)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind AVX2 NEON and RVV evidence to the admitted Stage-4 build (NFR-012)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject implicit or mismatched build provenance (NFR-012)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject implicit or mismatched build provenance (NFR-012)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:133:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate Vulkan candidate configuration before backend admission (NFR-012)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should validate Vulkan candidate configuration before backend admission (NFR-012)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:150:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep source verification out of the operation hot path (NFR-012)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include the SIMD runtime in pure-Simple native builds (NFR-012)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/crypto/x25519mlkem768_simd_provenance_contract_spec.spl:180:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require admission and report the observed SIMD path without GPU claims (NFR-012)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
