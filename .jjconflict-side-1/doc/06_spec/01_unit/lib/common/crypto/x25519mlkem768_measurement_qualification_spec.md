# X25519mlkem768 Measurement Qualification Specification

> Tests covering X25519MLKEM768 matrix-bound measurement qualification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Measurement Qualification Specification

## Scenarios

### X25519MLKEM768 matrix-bound measurement qualification

#### mints a deterministic public-only CUDA qualification

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- mints a deterministic public-only CUDA qualification
- Re-admit all seven source rows inside the qualification owner
   - Expected: receipt.qualification_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mints a deterministic public-only CUDA qualification")
step("Re-admit all seven source rows inside the qualification owner")
val rows = _qualification_rows()
val target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Cuda)
val result = _qualification_admit(rows, target)
match result:
    case Err(reason): fail(reason)
    case Ok(receipt):
        expect(x25519_mlkem768_measurement_qualification_valid(
            receipt)).to_be(true)
        expect(receipt.qualification_sha256.len()).to_equal(64)
        expect(receipt.target.matrix_row_set_sha256).to_equal(
            x25519_mlkem768_admit_source_backend_matrix(
                rows).row_set_sha256)
        val rendered =
            x25519_mlkem768_render_measurement_qualification(receipt)
        expect(rendered.contains("shared_secret_sha256")).to_be(false)
        expect(rendered.contains("recovered_secret_sha256")).to_be(false)
        expect(rendered.contains(
            "accelerator_build_binding_sha256=" + "4" * 64
            )).to_be(true)
```

</details>

#### requires an exact lower-hex build binding only for GPU targets

- requires an exact lower-hex build binding only for GPU targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires an exact lower-hex build binding only for GPU targets")
val rows = _qualification_rows()
var missing = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Cuda)
missing.accelerator_build_binding_sha256 = ""
expect(_qualification_admit(rows, missing).unwrap_err()).to_equal(
    "accelerator-build-binding-sha256-required")

var malformed = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Vulkan)
malformed.accelerator_build_binding_sha256 = "A" * 64
expect(_qualification_admit(rows, malformed).unwrap_err()).to_equal(
    "accelerator-build-binding-sha256-invalid")

var unexpected = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Neon)
unexpected.accelerator_build_binding_sha256 = "4" * 64
expect(_qualification_admit(rows, unexpected).unwrap_err()).to_equal(
    "accelerator-build-binding-sha256-unexpected")
```

</details>

#### binds the GPU build binding into the qualification hash

- binds the GPU build binding into the qualification hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds the GPU build binding into the qualification hash")
val rows = _qualification_rows()
val target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Metal)
val receipt = _qualification_admit(rows, target).unwrap()
var changed = receipt
changed.target.accelerator_build_binding_sha256 = "8" * 64
expect(x25519_mlkem768_measurement_qualification_sha256(
    changed) == receipt.qualification_sha256).to_be(false)
expect(x25519_mlkem768_measurement_qualification_valid(
    changed)).to_be(false)
```

</details>

#### rejects every live observation binding mismatch

- rejects every live observation binding mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects every live observation binding mismatch")
val rows = _qualification_rows()
val target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Cuda)
val base = _qualification_observation(target)

var bad_digest = base
bad_digest.observation_sha256 = "8" * 64
expect(x25519_mlkem768_qualify_measurement(
    rows, target, bad_digest).unwrap_err()).to_equal(
    "platform-measurement-observation-mismatch")

var wrong_host = base
wrong_host.host_os = "freebsd"
wrong_host = _qualification_rehash_observation(wrong_host)
expect(x25519_mlkem768_qualify_measurement(
    rows, target, wrong_host).is_err()).to_be(true)

var wrong_arch = base
wrong_arch.host_arch = "aarch64"
wrong_arch = _qualification_rehash_observation(wrong_arch)
expect(x25519_mlkem768_qualify_measurement(
    rows, target, wrong_arch).is_err()).to_be(true)

var wrong_session = base
wrong_session.session_nonce_sha256 = "8" * 64
wrong_session = _qualification_rehash_observation(wrong_session)
expect(x25519_mlkem768_qualify_measurement(
    rows, target, wrong_session).is_err()).to_be(true)

var wrong_artifact = base
wrong_artifact.observer_artifact_sha256 = "8" * 64
wrong_artifact = _qualification_rehash_observation(wrong_artifact)
expect(x25519_mlkem768_qualify_measurement(
    rows, target, wrong_artifact).is_err()).to_be(true)

var wrong_clock = base
wrong_clock.clock_source = "different-clock"
wrong_clock = _qualification_rehash_observation(wrong_clock)
expect(x25519_mlkem768_qualify_measurement(
    rows, target, wrong_clock).is_err()).to_be(true)

var guest_heap = base
guest_heap.peak_memory_metric =
    PlatformPeakMemoryMetric.GuestHeapCommittedHighWaterKiB
guest_heap = _qualification_rehash_observation(guest_heap)
expect(x25519_mlkem768_qualify_measurement(
    rows, target, guest_heap).is_err()).to_be(true)
```

</details>

#### rejects scalar and non-physical capture targets

- rejects scalar and non-physical capture targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects scalar and non-physical capture targets")
val rows = _qualification_rows()
var scalar_target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Cuda)
scalar_target.backend = X25519MlKem768EvidenceBackend.ScalarCpu
expect(_qualification_admit(
    rows, scalar_target).unwrap_err()).to_equal(
    "specialized-measurement-backend-required")
var synthetic_target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Avx2)
synthetic_target.capture_kind = X25519MlKem768CaptureKind.Synthetic
expect(_qualification_admit(
    rows, synthetic_target).unwrap_err()).to_equal(
    "native-physical-full-operation-capture-required")
```

</details>

#### rejects stale row-set and exact target binding

- rejects stale row-set and exact target binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects stale row-set and exact target binding")
val rows = _qualification_rows()
var stale = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Rvv)
stale.matrix_row_set_sha256 = "7" * 64
expect(_qualification_admit(
    rows, stale).unwrap_err()).to_equal(
    "matrix-row-set-sha256-mismatch")
var artifact = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Vulkan)
artifact.backend_artifact_sha256 = "8" * 64
expect(_qualification_admit(
    rows, artifact).unwrap_err()).to_equal(
    "measurement-target-row-binding-mismatch")
var scalar_artifact = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Vulkan)
scalar_artifact.scalar_backend_artifact_sha256 = "8" * 64
expect(_qualification_admit(
    rows, scalar_artifact).unwrap_err()).to_equal(
    "measurement-target-scalar-row-binding-mismatch")
```

</details>

<details>
<summary>Advanced: rejects malformed session identity before matrix admission</summary>

#### rejects malformed session identity before matrix admission

- rejects malformed session identity before matrix admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed session identity before matrix admission")
val rows = _qualification_rows()
var target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Neon)
target.session_id = "session\nstatus=pass"
expect(_qualification_admit(
    rows, target).unwrap_err()).to_equal(
    "measurement-target-text-field-invalid")
```

</details>


</details>

#### rejects a mutated typed public set during internal re-admission

- rejects a mutated typed public set during internal re-admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a mutated typed public set during internal re-admission")
var rows = _qualification_rows()
val target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Cuda)
var changed = _qualification_set_b()
changed.first_output_sha256 = "7" * 64
rows[4].set_b = Some(changed)
expect(_qualification_admit(
    rows, target).unwrap_err()).to_equal(
    "complete-admitted-matrix-required")
```

</details>

#### invalidates qualification after any retained field mutation

- invalidates qualification after any retained field mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invalidates qualification after any retained field mutation")
val rows = _qualification_rows()
val target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Metal)
val receipt = _qualification_admit(
    rows, target).unwrap()
var changed = receipt
changed.target.monotonic_clock_id = "different-clock"
expect(x25519_mlkem768_measurement_qualification_valid(
    changed)).to_be(false)
```

</details>

#### rejects semantically invalid qualification even after canonical rehash

- rejects semantically invalid qualification even after canonical rehash


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects semantically invalid qualification even after canonical rehash")
val rows = _qualification_rows()
val target = _qualification_target(
    rows, X25519MlKem768EvidenceBackend.Avx2)
val receipt = _qualification_admit(
    rows, target).unwrap()
var wrong_profile = receipt
wrong_profile.profile_version = "attacker-controlled-profile"
wrong_profile.qualification_sha256 =
    x25519_mlkem768_measurement_qualification_sha256(wrong_profile)
expect(x25519_mlkem768_measurement_qualification_valid(
    wrong_profile)).to_be(false)
var wrong_set = receipt
wrong_set.set_c.first_output_bytes = 1
wrong_set.qualification_sha256 =
    x25519_mlkem768_measurement_qualification_sha256(wrong_set)
expect(x25519_mlkem768_measurement_qualification_valid(
    wrong_set)).to_be(false)
var permuted_sets = receipt
val original_set_a = permuted_sets.set_a
permuted_sets.set_a = permuted_sets.set_b
permuted_sets.set_b = original_set_a
permuted_sets.qualification_sha256 =
    x25519_mlkem768_measurement_qualification_sha256(permuted_sets)
expect(x25519_mlkem768_measurement_qualification_valid(
    permuted_sets)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 matrix-bound measurement qualification.
- X25519MLKEM768 matrix-bound measurement qualification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `3dff36039ef2890fe4bb0da9c8a038cd4f60d4bf0b95cd7cab2687bef52d0e50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3dff36039ef2890fe4bb0da9c8a038cd4f60d4bf0b95cd7cab2687bef52d0e50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3dff36039ef2890fe4bb0da9c8a038cd4f60d4bf0b95cd7cab2687bef52d0e50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl:241:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mints a deterministic public-only CUDA qualification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl:266:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires an exact lower-hex build binding only for GPU targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/x25519mlkem768_measurement_qualification_spec.spl:288:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the GPU build binding into the qualification hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
