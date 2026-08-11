# X25519mlkem768 Pinned Workload Specification

> Tests covering X25519MLKEM768 canonical pinned A/B/C workload, X25519MLKEM768 pinned Set A ML-KEM receipt, X25519MLKEM768 pinned Set B X25519 receipt, X25519MLKEM768 pinned Set C hybrid receipt, X25519MLKEM768 pinned SIMD rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Pinned Workload Specification

## Scenarios

### X25519MLKEM768 canonical pinned A/B/C workload

#### returns only pinned public identities lengths statuses and digests

- Run deterministic ML-KEM-768 and RFC 7748 composition
- x25519 mlkem768 pinned scalar config
- Compare 2336 public-wire and 2400 total observed bytes
   - Expected: outputs.set_a.first_output_bytes equals `1184`
   - Expected: outputs.set_a.second_output_bytes equals `1088`
   - Expected: outputs.set_b.first_output_bytes equals `32`
   - Expected: outputs.set_b.second_output_bytes equals `32`
   - Expected: outputs.set_c.shared_secret_bytes equals `64`
   - Expected: outputs.artifact_digest equals ``
   - Expected: outputs.accelerated_operation_count equals `0`
   - Expected: outputs.kernel_invocations equals `0`
   - Expected: outputs.simd_chunk_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        expect(outputs.oracle_id).to_equal(
            X25519_MLKEM768_PINNED_ORACLE_ID)
        expect(outputs.set_a.set_id).to_equal(
            X25519MlKem768PinnedSet.MlKem)
        expect(outputs.set_b.set_id).to_equal(
            X25519MlKem768PinnedSet.X25519)
        expect(outputs.set_c.set_id).to_equal(
            X25519MlKem768PinnedSet.Hybrid)
        expect(outputs.set_a.first_output_bytes).to_equal(1184)
        expect(outputs.set_a.second_output_bytes).to_equal(1088)
        expect(outputs.set_b.first_output_bytes).to_equal(32)
        expect(outputs.set_b.second_output_bytes).to_equal(32)
        expect(outputs.set_c.shared_secret_bytes).to_equal(64)
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
        expect(outputs.accelerated_operation_count).to_equal(0)
        expect(outputs.kernel_invocations).to_equal(0)
        expect(outputs.simd_chunk_hits).to_equal(0)
        expect(outputs.compiled).to_be(false)
        expect(outputs.submitted).to_be(false)
        expect(outputs.fence_completed).to_be(false)
        expect(outputs.device_readback).to_be(false)
    case Err(reason): fail(reason)
```

</details>

### X25519MLKEM768 pinned Set A ML-KEM receipt

#### constructs the exact independently validated ML-KEM receipt

- Validate EK CT and both 32-byte ML-KEM shared secrets
   - Expected: receipt.first_output_bytes equals `1184`
   - Expected: receipt.second_output_bytes equals `1088`
   - Expected: receipt.shared_secret_bytes equals `32`
   - Expected: receipt.recovered_secret_bytes equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate EK CT and both 32-byte ML-KEM shared secrets")
match x25519_mlkem768_validate_pinned_set_a(_set_a_checks()):
    case Ok(receipt):
        expect(receipt.set_id).to_equal(
            X25519MlKem768PinnedSet.MlKem)
        expect(receipt.first_output_label).to_equal(
            "mlkem768-encapsulation-key")
        expect(receipt.second_output_label).to_equal(
            "mlkem768-ciphertext")
        expect(receipt.first_output_bytes).to_equal(1184)
        expect(receipt.second_output_bytes).to_equal(1088)
        expect(receipt.shared_secret_bytes).to_equal(32)
        expect(receipt.recovered_secret_bytes).to_equal(32)
    case Err(reason): fail(reason)
```

</details>

#### rejects identity EK length EK digest and ML-KEM secret drift

- Reject a Set B observation presented as Set A
- var wrong identity =  set a checks
-  expect error
- Reject the 1183/1184 EK truncation boundary
- var short ek =  set a checks
-  expect error
- Reject exact EK content drift
- var wrong ek =  set a checks
-  expect error
- Reject encapsulated and recovered ML-KEM secret drift
- var wrong shared =  set a checks
-  expect error
- var wrong recovered =  set a checks
-  expect error


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Validate client public server public and both X25519 secrets
   - Expected: receipt.first_output_bytes equals `32`
   - Expected: receipt.second_output_bytes equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate client public server public and both X25519 secrets")
match x25519_mlkem768_validate_pinned_set_b(_set_b_checks()):
    case Ok(receipt):
        expect(receipt.set_id).to_equal(
            X25519MlKem768PinnedSet.X25519)
        expect(receipt.first_output_label).to_equal(
            "x25519-client-public")
        expect(receipt.second_output_label).to_equal(
            "x25519-server-public")
        expect(receipt.first_output_bytes).to_equal(32)
        expect(receipt.second_output_bytes).to_equal(32)
    case Err(reason): fail(reason)
```

</details>

#### rejects server-public length digest recovered and roundtrip drift

- Reject the 31/32 server-public truncation boundary
- var short server public =  set b checks
- x25519 mlkem768 validate pinned set b
- Reject exact server-public content drift
- var wrong server public =  set b checks
- x25519 mlkem768 validate pinned set b
- Reject recovered X25519 oracle drift
- var wrong recovered =  set b checks
-  expect error
- Reject an unequal encapsulated and recovered X25519 secret
- var wrong roundtrip =  set b checks
-  expect error


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Validate full shares and both 64-byte hybrid secrets
   - Expected: receipt.first_output_bytes equals `1216`
   - Expected: receipt.second_output_bytes equals `1120`
   - Expected: receipt.shared_secret_bytes equals `64`
   - Expected: receipt.recovered_secret_bytes equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate full shares and both 64-byte hybrid secrets")
match x25519_mlkem768_validate_pinned_set_c(_set_c_checks()):
    case Ok(receipt):
        expect(receipt.set_id).to_equal(
            X25519MlKem768PinnedSet.Hybrid)
        expect(receipt.first_output_bytes).to_equal(1216)
        expect(receipt.second_output_bytes).to_equal(1120)
        expect(receipt.shared_secret_bytes).to_equal(64)
        expect(receipt.recovered_secret_bytes).to_equal(64)
    case Err(reason): fail(reason)
```

</details>

#### rejects hybrid shared and recovered length drift before slicing

- Reject a 63-byte hybrid secret
- var short shared =  set c checks
-  expect error
- Reject a 63-byte recovered hybrid secret
- var short recovered =  set c checks
-  expect error


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Require the typed AVX2 candidate without Stage-4 admission
- Require the typed NEON candidate without Stage-4 admission
- Require the typed RVV candidate without Stage-4 admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 canonical pinned A/B/C workload, X25519MLKEM768 pinned Set A ML-KEM receipt, X25519MLKEM768 pinned Set B X25519 receipt, X25519MLKEM768 pinned Set C hybrid receipt, X25519MLKEM768 pinned SIMD rows.
- X25519MLKEM768 canonical pinned A/B/C workload
- X25519MLKEM768 pinned Set A ML-KEM receipt
- X25519MLKEM768 pinned Set B X25519 receipt
- X25519MLKEM768 pinned Set C hybrid receipt
- X25519MLKEM768 pinned SIMD rows

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
