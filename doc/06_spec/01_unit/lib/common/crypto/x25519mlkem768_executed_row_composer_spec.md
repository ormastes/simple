# X25519mlkem768 Executed Row Composer Specification

> Tests covering X25519MLKEM768 executed matrix row composer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Executed Row Composer Specification

## Scenarios

### X25519MLKEM768 executed matrix row composer

#### constructs a complete executed row from public typed receipts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs a complete executed row from public typed receipts
- Compose a CUDA row after all public evidence is present
   - Expected: row.public_wire_bytes equals `2336`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs a complete executed row from public typed receipts")
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

- rejects a run receipt that did not pass
- Change the executed status to blocked
   - Expected: result.unwrap_err() equals `execution-status-not-pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a run receipt that did not pass")
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

- rejects backend selection that differs from the request
- Claim AVX2 selection for a CUDA request
   - Expected: result.unwrap_err() equals `fallback-or-selection-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects backend selection that differs from the request")
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

- rejects an incomplete GPU device proof
- Remove the device readback lifecycle event
   - Expected: result.unwrap_err() equals `gpu-device-proof-incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an incomplete GPU device proof")
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

- rejects an artifact not bound to the execution receipt
- Use a different admitted CUDA binary digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an artifact not bound to the execution receipt")
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

- rejects an incomplete or mislabeled typed set receipt
- Remove the canonical Set B public-output label


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an incomplete or mislabeled typed set receipt")
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

- rejects Set C when it does not bind the supplied public output
- Supply a different client-share digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects Set C when it does not bind the supplied public output")
step("Supply a different client-share digest")
val result = _compose(_composer_execution(), _composer_set_a(),
    _composer_set_b(), _composer_set_c(), "7" * 64)
expect(result.unwrap_err()).to_equal(
    "set-c-public-wire-sha256-mismatch")
```

</details>

#### rejects malformed public provenance without exposing secret hashes

- rejects malformed public provenance without exposing secret hashes
- Use an uppercase runner artifact digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed public provenance without exposing secret hashes")
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

<details>
<summary>Advanced: rejects an empty pinned workload digest before accepting a matrix row</summary>

#### rejects an empty pinned workload digest before accepting a matrix row

- rejects an empty pinned workload digest before accepting a matrix row


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an empty pinned workload digest before accepting a matrix row")
var execution = _composer_execution()
execution.pinned_workload_sha256 = ""
val result = _compose(execution, _composer_set_a(), _composer_set_b(),
    _composer_set_c(), X25519_MLKEM768_PINNED_CLIENT_SHARE_SHA256)
expect(result.unwrap_err()).to_equal(
    "pinned-workload-or-fixture-provenance-sha256-invalid")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 executed matrix row composer.
- X25519MLKEM768 executed matrix row composer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-008`
- `REQ-009`
- `REQ-010`
- `REQ-012`
- `REQ-015`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a60e57e907ba521cbf33e5dfd804a724a8fa733dfacd4b8ea3b4c4c6e08ae4e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a60e57e907ba521cbf33e5dfd804a724a8fa733dfacd4b8ea3b4c4c6e08ae4e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a60e57e907ba521cbf33e5dfd804a724a8fa733dfacd4b8ea3b4c4c6e08ae4e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a complete executed row from public typed receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a run receipt that did not pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_executed_row_composer_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects backend selection that differs from the request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
