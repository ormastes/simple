# x25519mlkem768_pinned_workload_spec

> Verifies the x25519mlkem768 pinned workload behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_pinned_workload_spec

Verifies the x25519mlkem768 pinned workload behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the x25519mlkem768 pinned workload behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### X25519MLKEM768 canonical pinned A/B/C workload

#### binds the exact full-hybrid inputs with explicit m equals d

- Verify: binds the exact full-hybrid inputs with explicit m equals d
- Derive the non-secret domain-separated pinned workload digest
   - Expected: digest equals `X25519_MLKEM768_PINNED_WORKLOAD_SHA256`
- Accept only the pinned fixture identity and its digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: binds the exact full-hybrid inputs with explicit m equals d")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Derive the non-secret domain-separated pinned workload digest")
match x25519_mlkem768_pinned_workload_sha256():
    case Ok(digest):
        expect(digest).to_equal(X25519_MLKEM768_PINNED_WORKLOAD_SHA256)
        step("Accept only the pinned fixture identity and its digest")
        expect(x25519_mlkem768_pinned_workload_binding_reason(
            X25519_MLKEM768_PINNED_FIXTURE_ID, digest)).to_equal("")
    case Err(reason): fail(reason)
```

</details>

#### rejects a mixed fixture identity or raw-workload digest

- Verify: rejects a mixed fixture identity or raw-workload digest
- Reject a canonical NTT fixture identity for the full workload
- Reject a digest from any other five-input workload


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: rejects a mixed fixture identity or raw-workload digest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject a canonical NTT fixture identity for the full workload")
expect(x25519_mlkem768_pinned_workload_binding_reason(
    "x25519mlkem768-v1", X25519_MLKEM768_PINNED_WORKLOAD_SHA256
)).to_equal("pinned-workload-fixture-id-mismatch")
step("Reject a digest from any other five-input workload")
expect(x25519_mlkem768_pinned_workload_binding_reason(
    X25519_MLKEM768_PINNED_FIXTURE_ID, "0" * 64
)).to_equal("pinned-workload-sha256-mismatch")
```

</details>

#### returns only pinned public identities lengths statuses and digests

- Verify: returns only pinned public identities lengths statuses and digests
- Run deterministic ML-KEM-768 and RFC 7748 composition
- Compare 2336 public-wire and 2400 total observed bytes
   - Expected: outputs.set_a.first_output_bytes equals `1184)  # oracle: pinned constant asserted by this scenario`
   - Expected: outputs.set_a.second_output_bytes equals `1088)  # oracle: pinned constant asserted by this scenario`
   - Expected: outputs.set_b.first_output_bytes equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: outputs.set_b.second_output_bytes equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: outputs.set_c.shared_secret_bytes equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: outputs.artifact_digest equals ``
   - Expected: outputs.accelerated_operation_count equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: outputs.kernel_invocations equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: outputs.simd_chunk_hits equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: returns only pinned public identities lengths statuses and digests")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Run deterministic ML-KEM-768 and RFC 7748 composition")
val result = x25519_mlkem768_run_pinned_workload(
    x25519_mlkem768_pinned_scalar_config())
match result:
    case Ok(outputs):
        step("Compare 2336 public-wire and 2400 total observed bytes")
        expect(outputs.schema).to_equal(
            X25519_MLKEM768_PINNED_WORKLOAD_SCHEMA)
        expect(outputs.fixture_id).to_equal(
            X25519_MLKEM768_PINNED_FIXTURE_ID)
        expect(outputs.workload_sha256).to_equal(
            X25519_MLKEM768_PINNED_WORKLOAD_SHA256)
        expect(outputs.oracle_id).to_equal(
            X25519_MLKEM768_PINNED_ORACLE_ID)
        expect(outputs.set_a.set_id).to_equal(
            X25519MlKem768PinnedSet.MlKem)
        expect(outputs.set_b.set_id).to_equal(
            X25519MlKem768PinnedSet.X25519)
        expect(outputs.set_c.set_id).to_equal(
            X25519MlKem768PinnedSet.Hybrid)
        expect(outputs.set_a.first_output_bytes).to_equal(1184)  # oracle: pinned constant asserted by this scenario
        expect(outputs.set_a.second_output_bytes).to_equal(1088)  # oracle: pinned constant asserted by this scenario
        expect(outputs.set_b.first_output_bytes).to_equal(32)  # oracle: pinned constant asserted by this scenario
        expect(outputs.set_b.second_output_bytes).to_equal(32)  # oracle: pinned constant asserted by this scenario
        expect(outputs.set_c.shared_secret_bytes).to_equal(64)  # oracle: pinned constant asserted by this scenario
        expect(outputs.public_wire_bytes).to_equal(
            X25519_MLKEM768_PINNED_PUBLIC_WIRE_BYTES)
        expect(outputs.total_observed_bytes).to_equal(
            X25519_MLKEM768_PINNED_TOTAL_OBSERVED_BYTES)
        expect(outputs.client_share_sha256).to_equal(
            X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
        expect(outputs.server_share_sha256).to_equal(
            X25519_MLKEM768_PINNED_SERVER_SHARE_SHA256)
        expect(outputs.keygen_output_digest).to_equal(
            X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
        expect(outputs.encapsulate_output_digest).to_equal(
            X25519_MLKEM768_PINNED_SERVER_SHARE_SHA256)
        expect(outputs.decapsulate_output_digest).to_equal(
            X25519_MLKEM768_PINNED_SERVER_SHARE_SHA256)
        expect(outputs.requested_backend).to_equal(
            X25519MlKem768Backend.ScalarCpu)
        expect(outputs.selected_backend).to_equal(
            X25519MlKem768Backend.ScalarCpu)
        expect(outputs.executor_identity).to_equal(
            "pure-simple-scalar")
        expect(outputs.artifact_digest).to_equal("")
        expect(outputs.execution_proof_digest).to_equal(
            X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
        expect(outputs.fallback_used).to_be(false)
        expect(outputs.candidate_oracle_match).to_be(false)
        expect(outputs.accelerated_operation_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
        expect(outputs.kernel_invocations).to_equal(0)  # oracle: pinned constant asserted by this scenario
        expect(outputs.simd_chunk_hits).to_equal(0)  # oracle: pinned constant asserted by this scenario
        expect(outputs.compiled).to_be(false)
        expect(outputs.submitted).to_be(false)
        expect(outputs.fence_completed).to_be(false)
        expect(outputs.device_readback).to_be(false)
    case Err(reason): fail(reason)
```

</details>

#### propagates pinned identity and digests into scalar and AVX2 full receipts

- Verify: propagates pinned identity and digests into scalar and AVX2 full receipts
- Run the pinned scalar workload once for public receipt values
- Bind pinned values into the scalar full-operation receipt
   - Expected: scalar.fixture_id equals `X25519_MLKEM768_PINNED_FIXTURE_ID`
   - Expected: scalar.pinned_workload_sha256 equals `outputs.workload_sha256`
   - Expected: scalar.keygen_output_digest equals `outputs.keygen_output_digest`
- Bind those same pinned public values into the AVX2 receipt
   - Expected: avx2.fixture_id equals `X25519_MLKEM768_PINNED_FIXTURE_ID`
   - Expected: avx2.pinned_workload_sha256 equals `outputs.workload_sha256`
   - Expected: avx2.keygen_output_digest equals `outputs.keygen_output_digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: propagates pinned identity and digests into scalar and AVX2 full receipts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Run the pinned scalar workload once for public receipt values")
val outputs = match x25519_mlkem768_run_pinned_workload(
        x25519_mlkem768_pinned_scalar_config()):
    case Ok(value): value
    case Err(reason): fail(reason)
val scalar_cli = X25519MlKem768EvidenceCli(
    fixture_manifest: "manifest.sdn", fixture_source: "fixture.spl",
    runner_source: "runner.spl",
    backend: X25519MlKem768EvidenceBackend.ScalarCpu,
    mode: X25519MlKem768EvidenceMode.Native,
    scope: X25519MlKem768EvidenceScope.FullOperation,
    batch_size: 1)
step("Bind pinned values into the scalar full-operation receipt")
val scalar = x25519_mlkem768_pinned_full_operation_receipt(
    scalar_cli, "a" * 64, "b" * 64, "c" * 64,
    "scalar-pinned-full-operation-admitted", outputs)
expect(scalar.fixture_id).to_equal(X25519_MLKEM768_PINNED_FIXTURE_ID)
expect(scalar.pinned_workload_sha256).to_equal(outputs.workload_sha256)
expect(scalar.keygen_output_digest).to_equal(outputs.keygen_output_digest)
expect(scalar.encapsulate_output_digest).to_equal(
    outputs.encapsulate_output_digest)
expect(scalar.decapsulate_output_digest).to_equal(
    outputs.decapsulate_output_digest)
expect(scalar.absolute_oracle_match).to_be(true)
step("Bind those same pinned public values into the AVX2 receipt")
val avx2_cli = X25519MlKem768EvidenceCli(
    fixture_manifest: "manifest.sdn", fixture_source: "fixture.spl",
    runner_source: "runner.spl",
    backend: X25519MlKem768EvidenceBackend.Avx2,
    mode: X25519MlKem768EvidenceMode.Native,
    scope: X25519MlKem768EvidenceScope.FullOperation,
    batch_size: 1)
val avx2 = x25519_mlkem768_pinned_full_operation_receipt(
    avx2_cli, "a" * 64, "b" * 64, "c" * 64,
    "native-simd-pinned-full-operation-admitted", outputs)
expect(avx2.fixture_id).to_equal(X25519_MLKEM768_PINNED_FIXTURE_ID)
expect(avx2.pinned_workload_sha256).to_equal(outputs.workload_sha256)
expect(avx2.keygen_output_digest).to_equal(outputs.keygen_output_digest)
expect(avx2.selected_backend).to_equal(
    Some(X25519MlKem768EvidenceBackend.Avx2))
```

</details>

#### hands native SIMD A/B/C public outputs to later composition without promotion

- Verify: hands native SIMD A/B/C public outputs to later composition without promotion
- Create a public-only AVX2-shaped pinned output observation
- Preserve exact workload digest and all three public set receipts
   - Expected: observation.set_a equals `outputs.set_a`
   - Expected: observation.set_b equals `outputs.set_b`
   - Expected: observation.set_c equals `outputs.set_c`
- Keep the raw runner receipt explicitly non-promotable


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: hands native SIMD A/B/C public outputs to later composition without promotion")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create a public-only AVX2-shaped pinned output observation")
var outputs = match x25519_mlkem768_run_pinned_workload(
        x25519_mlkem768_pinned_scalar_config()):
    case Ok(value): value
    case Err(reason): fail(reason)
outputs.requested_backend = X25519MlKem768Backend.Avx2
outputs.selected_backend = X25519MlKem768Backend.Avx2
outputs.executor_identity = "native-avx2-candidate"
outputs.artifact_digest = "d" * 64
outputs.execution_proof_digest = "d" * 64
outputs.candidate_oracle_match = true
outputs.accelerated_operation_count = 3
outputs.simd_chunk_hits = 3
val cli = X25519MlKem768EvidenceCli(
    fixture_manifest: "manifest.sdn", fixture_source: "fixture.spl",
    runner_source: "runner.spl",
    backend: X25519MlKem768EvidenceBackend.Avx2,
    mode: X25519MlKem768EvidenceMode.Native,
    scope: X25519MlKem768EvidenceScope.FullOperation,
    batch_size: 1)
step("Preserve exact workload digest and all three public set receipts")
val observation = match x25519_mlkem768_pinned_simd_observation_from_outputs(
        cli, "a" * 64, "b" * 64, "c" * 64, outputs):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(observation.raw_receipt.pinned_workload_sha256).to_equal(
    X25519_MLKEM768_PINNED_WORKLOAD_SHA256)
expect(observation.public_outputs.workload_sha256).to_equal(
    X25519_MLKEM768_PINNED_WORKLOAD_SHA256)
expect(observation.set_a).to_equal(outputs.set_a)
expect(observation.set_b).to_equal(outputs.set_b)
expect(observation.set_c).to_equal(outputs.set_c)
expect(observation.client_share_sha256).to_equal(
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
expect(observation.server_share_sha256).to_equal(
    X25519_MLKEM768_PINNED_SERVER_SHARE_SHA256)
step("Keep the raw runner receipt explicitly non-promotable")
expect(observation.raw_receipt.promotion_eligible).to_be(false)
expect(observation.raw_receipt.reason).to_equal(
    "native-simd-pinned-full-operation-observed")
```

</details>

### X25519MLKEM768 pinned Set A ML-KEM receipt

#### constructs the exact independently validated ML-KEM receipt

- Verify: constructs the exact independently validated ML-KEM receipt
- Validate EK CT and both 32-byte ML-KEM shared secrets
   - Expected: receipt.first_output_bytes equals `1184)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.second_output_bytes equals `1088)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.shared_secret_bytes equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.recovered_secret_bytes equals `32)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: constructs the exact independently validated ML-KEM receipt")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Validate EK CT and both 32-byte ML-KEM shared secrets")
match x25519_mlkem768_validate_pinned_set_a(_set_a_checks()):
    case Ok(receipt):
        expect(receipt.set_id).to_equal(
            X25519MlKem768PinnedSet.MlKem)
        expect(receipt.first_output_label).to_equal(
            "mlkem768-encapsulation-key")
        expect(receipt.second_output_label).to_equal(
            "mlkem768-ciphertext")
        expect(receipt.first_output_bytes).to_equal(1184)  # oracle: pinned constant asserted by this scenario
        expect(receipt.second_output_bytes).to_equal(1088)  # oracle: pinned constant asserted by this scenario
        expect(receipt.shared_secret_bytes).to_equal(32)  # oracle: pinned constant asserted by this scenario
        expect(receipt.recovered_secret_bytes).to_equal(32)  # oracle: pinned constant asserted by this scenario
    case Err(reason): fail(reason)
```

</details>

#### rejects identity EK length EK digest and ML-KEM secret drift

- Verify: rejects identity EK length EK digest and ML-KEM secret drift
- Reject a Set B observation presented as Set A
- Reject the 1183/1184 EK truncation boundary
- Reject exact EK content drift
- Reject encapsulated and recovered ML-KEM secret drift


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: rejects identity EK length EK digest and ML-KEM secret drift")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject a Set B observation presented as Set A")
var wrong_identity = _set_a_checks()
wrong_identity.set_id = X25519MlKem768PinnedSet.X25519
_expect_error(x25519_mlkem768_validate_pinned_set_a(wrong_identity),
    "pinned-set-a-identity-mismatch")
step("Reject the 1183/1184 EK truncation boundary")
var short_ek = _set_a_checks()
short_ek.first_output_bytes = 1183
_expect_error(x25519_mlkem768_validate_pinned_set_a(short_ek),
    "pinned-set-a-first-output-length-mismatch")
step("Reject exact EK content drift")
var wrong_ek = _set_a_checks()
wrong_ek.first_output_sha256 = "0" * 64
_expect_error(x25519_mlkem768_validate_pinned_set_a(wrong_ek),
    "pinned-set-a-first-output-mismatch")
step("Reject encapsulated and recovered ML-KEM secret drift")
var wrong_shared = _set_a_checks()
wrong_shared.shared_secret_oracle_match = false
_expect_error(x25519_mlkem768_validate_pinned_set_a(wrong_shared),
    "pinned-set-a-shared-secret-oracle-mismatch")
var wrong_recovered = _set_a_checks()
wrong_recovered.recovered_secret_oracle_match = false
_expect_error(x25519_mlkem768_validate_pinned_set_a(wrong_recovered),
    "pinned-set-a-recovered-secret-oracle-mismatch")
```

</details>

### X25519MLKEM768 pinned Set B X25519 receipt

#### constructs the exact independently validated X25519 receipt

- Verify: constructs the exact independently validated X25519 receipt
- Validate client public server public and both X25519 secrets
   - Expected: receipt.first_output_bytes equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.second_output_bytes equals `32)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: constructs the exact independently validated X25519 receipt")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Validate client public server public and both X25519 secrets")
match x25519_mlkem768_validate_pinned_set_b(_set_b_checks()):
    case Ok(receipt):
        expect(receipt.set_id).to_equal(
            X25519MlKem768PinnedSet.X25519)
        expect(receipt.first_output_label).to_equal(
            "x25519-client-public")
        expect(receipt.second_output_label).to_equal(
            "x25519-server-public")
        expect(receipt.first_output_bytes).to_equal(32)  # oracle: pinned constant asserted by this scenario
        expect(receipt.second_output_bytes).to_equal(32)  # oracle: pinned constant asserted by this scenario
    case Err(reason): fail(reason)
```

</details>

#### rejects server-public length digest recovered and roundtrip drift

- Verify: rejects server-public length digest recovered and roundtrip drift
- Reject the 31/32 server-public truncation boundary
- Reject exact server-public content drift
- Reject recovered X25519 oracle drift
- Reject an unequal encapsulated and recovered X25519 secret


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: rejects server-public length digest recovered and roundtrip drift")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject the 31/32 server-public truncation boundary")
var short_server_public = _set_b_checks()
short_server_public.second_output_bytes = 31
_expect_error(
    x25519_mlkem768_validate_pinned_set_b(short_server_public),
    "pinned-set-b-second-output-length-mismatch")
step("Reject exact server-public content drift")
var wrong_server_public = _set_b_checks()
wrong_server_public.second_output_sha256 = "f" * 64
_expect_error(
    x25519_mlkem768_validate_pinned_set_b(wrong_server_public),
    "pinned-set-b-second-output-mismatch")
step("Reject recovered X25519 oracle drift")
var wrong_recovered = _set_b_checks()
wrong_recovered.recovered_secret_oracle_match = false
_expect_error(x25519_mlkem768_validate_pinned_set_b(wrong_recovered),
    "pinned-set-b-recovered-secret-oracle-mismatch")
step("Reject an unequal encapsulated and recovered X25519 secret")
var wrong_roundtrip = _set_b_checks()
wrong_roundtrip.roundtrip_match = false
_expect_error(x25519_mlkem768_validate_pinned_set_b(wrong_roundtrip),
    "pinned-set-b-roundtrip-secret-mismatch")
```

</details>

### X25519MLKEM768 pinned Set C hybrid receipt

#### constructs the exact independently validated hybrid receipt

- Verify: constructs the exact independently validated hybrid receipt
- Validate full shares and both 64-byte hybrid secrets
   - Expected: receipt.first_output_bytes equals `1216)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.second_output_bytes equals `1120)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.shared_secret_bytes equals `64)  # oracle: pinned constant asserted by this scenario`
   - Expected: receipt.recovered_secret_bytes equals `64)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: constructs the exact independently validated hybrid receipt")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Validate full shares and both 64-byte hybrid secrets")
match x25519_mlkem768_validate_pinned_set_c(_set_c_checks()):
    case Ok(receipt):
        expect(receipt.set_id).to_equal(
            X25519MlKem768PinnedSet.Hybrid)
        expect(receipt.first_output_bytes).to_equal(1216)  # oracle: pinned constant asserted by this scenario
        expect(receipt.second_output_bytes).to_equal(1120)  # oracle: pinned constant asserted by this scenario
        expect(receipt.shared_secret_bytes).to_equal(64)  # oracle: pinned constant asserted by this scenario
        expect(receipt.recovered_secret_bytes).to_equal(64)  # oracle: pinned constant asserted by this scenario
    case Err(reason): fail(reason)
```

</details>

#### rejects hybrid shared and recovered length drift before slicing

- Verify: rejects hybrid shared and recovered length drift before slicing
- Reject a 63-byte hybrid secret
- Reject a 63-byte recovered hybrid secret


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: rejects hybrid shared and recovered length drift before slicing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject a 63-byte hybrid secret")
var short_shared = _set_c_checks()
short_shared.shared_secret_bytes = 63
_expect_error(x25519_mlkem768_validate_pinned_set_c(short_shared),
    "pinned-set-c-shared-secret-length-mismatch")
step("Reject a 63-byte recovered hybrid secret")
var short_recovered = _set_c_checks()
short_recovered.recovered_secret_bytes = 63
_expect_error(x25519_mlkem768_validate_pinned_set_c(short_recovered),
    "pinned-set-c-recovered-secret-length-mismatch")
```

</details>

### X25519MLKEM768 pinned SIMD rows

#### fails closed for every unadmitted AVX2 NEON and RVV row

- Verify: fails closed for every unadmitted AVX2 NEON and RVV row
- Require the typed AVX2 candidate without Stage-4 admission
- Require the typed NEON candidate without Stage-4 admission
- Require the typed RVV candidate without Stage-4 admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-003 REQ-013
step("Verify: fails closed for every unadmitted AVX2 NEON and RVV row")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Require the typed AVX2 candidate without Stage-4 admission")
_expect_unadmitted_simd_row_fails_closed(
    X25519MlKem768Backend.Avx2, "avx2")
step("Require the typed NEON candidate without Stage-4 admission")
_expect_unadmitted_simd_row_fails_closed(
    X25519MlKem768Backend.Neon, "neon")
step("Require the typed RVV candidate without Stage-4 admission")
_expect_unadmitted_simd_row_fails_closed(
    X25519MlKem768Backend.Rvv, "rvv")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a443ada37388df41fc7596abc8df049f2b8f03e71b5025a34212f387d793d37b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a443ada37388df41fc7596abc8df049f2b8f03e71b5025a34212f387d793d37b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a443ada37388df41fc7596abc8df049f2b8f03e71b5025a34212f387d793d37b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
