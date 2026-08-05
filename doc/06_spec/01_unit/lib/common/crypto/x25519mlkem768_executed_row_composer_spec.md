# X25519mlkem768 Executed Row Composer Specification

> Tests covering X25519MLKEM768 executed matrix row composer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Executed Row Composer Specification

## Scenarios

### X25519MLKEM768 executed matrix row composer

#### constructs a complete executed row from public typed receipts

- Compose a CUDA row after all public evidence is present
-  composer execution
-  composer set b
   - Expected: row.public_wire_bytes equals `2336`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compose a CUDA row after all public evidence is present")
val result = _compose(
    _composer_execution(), _composer_set_a(),
    _composer_set_b(), _composer_set_c(),
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
match result:
    case Err(reason): fail(reason)
    case Ok(row):
        expect(row.admission_phase).to_equal(
            X25519MlKem768MatrixAdmissionPhase.Executed)
        expect(row.public_wire_bytes).to_equal(2336)
        expect(row.pinned_workload_schema).to_equal(
            "x25519mlkem768-pinned-workload-v3")
        expect(row.set_a != nil).to_be(true)
        expect(row.set_b != nil).to_be(true)
        expect(row.set_c != nil).to_be(true)
```

</details>

#### rejects a run receipt that did not pass

- Change the executed status to blocked
- var execution =  composer execution
-  composer set b
   - Expected: result.unwrap_err() equals `execution-status-not-pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the executed status to blocked")
var execution = _composer_execution()
execution.status = X25519MlKem768EvidenceStatus.Blocked
execution.promotion_eligible = false
val result = _compose(execution, _composer_set_a(),
    _composer_set_b(), _composer_set_c(),
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
expect(result.is_err()).to_be(true)
expect(result.unwrap_err()).to_equal("execution-status-not-pass")
```

</details>

#### rejects backend selection that differs from the request

- Claim AVX2 selection for a CUDA request
- var execution =  composer execution
- execution selected backend = Some
-  composer set b
   - Expected: result.unwrap_err() equals `fallback-or-selection-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Claim AVX2 selection for a CUDA request")
var execution = _composer_execution()
execution.selected_backend = Some(X25519MlKem768EvidenceBackend.Avx2)
val result = _compose(execution, _composer_set_a(),
    _composer_set_b(), _composer_set_c(),
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
expect(result.unwrap_err()).to_equal("fallback-or-selection-mismatch")
```

</details>

#### rejects an incomplete GPU device proof

- Remove the device readback lifecycle event
- var execution =  composer execution
-  composer set b
   - Expected: result.unwrap_err() equals `gpu-device-proof-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the device readback lifecycle event")
var execution = _composer_execution()
execution.device_readback = false
val result = _compose(execution, _composer_set_a(),
    _composer_set_b(), _composer_set_c(),
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
expect(result.unwrap_err()).to_equal("gpu-device-proof-incomplete")
```

</details>

#### rejects an artifact not bound to the execution receipt

- Use a different admitted CUDA binary digest
-  composer execution
- "linux", "x86 64",  composer set a
-  composer set c


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use a different admitted CUDA binary digest")
val result = x25519_mlkem768_compose_executed_matrix_row(
    _composer_execution(), "9" * 64, "8" * 64,
    "linux", "x86_64", _composer_set_a(), _composer_set_b(),
    _composer_set_c(),
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256,
    X25519_MLKEM768_PINNED_SERVER_SHARE_SHA256)
expect(result.unwrap_err()).to_equal(
    "executed-artifact-binding-mismatch")
```

</details>

#### rejects an incomplete or mislabeled typed set receipt

- Remove the canonical Set B public-output label
- var set b =  composer set b
- set b,  composer set c


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove the canonical Set B public-output label")
var set_b = _composer_set_b()
set_b.first_output_label = ""
val result = _compose(_composer_execution(), _composer_set_a(),
    set_b, _composer_set_c(),
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
expect(result.unwrap_err()).to_equal(
    "set-b-set-public-output-label-mismatch")
```

</details>

#### rejects Set C when it does not bind the supplied public output

- Supply a different client-share digest
-  composer set b


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Supply a different client-share digest")
val result = _compose(_composer_execution(), _composer_set_a(),
    _composer_set_b(), _composer_set_c(), "7" * 64)
expect(result.unwrap_err()).to_equal(
    "set-c-public-wire-sha256-mismatch")
```

</details>

#### rejects malformed public provenance without exposing secret hashes

- Use an uppercase runner artifact digest
-  composer execution
- "linux", "x86 64",  composer set a
-  composer set c


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use an uppercase runner artifact digest")
val result = x25519_mlkem768_compose_executed_matrix_row(
    _composer_execution(), "A" * 64, "f" * 64,
    "linux", "x86_64", _composer_set_a(), _composer_set_b(),
    _composer_set_c(),
    X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256,
    X25519_MLKEM768_PINNED_SERVER_SHARE_SHA256)
expect(result.unwrap_err()).to_equal(
    "artifact-provenance-sha256-invalid")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 executed matrix row composer.
- X25519MLKEM768 executed matrix row composer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
