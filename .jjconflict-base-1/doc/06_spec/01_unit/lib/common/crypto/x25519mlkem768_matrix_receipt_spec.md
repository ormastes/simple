# X25519mlkem768 Matrix Receipt Specification

> Tests covering X25519MLKEM768 backend matrix v2.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Matrix Receipt Specification

## Scenarios

### X25519MLKEM768 backend matrix v2

#### admits seven typed native rows and hashes canonical backend order

- Admit synthetic branch-test rows with typed public receipts
-  complete matrix
   - Expected: receipt.status equals `X25519MlKem768EvidenceStatus.Pass`
   - Expected: receipt.admitted_rows equals `7`
   - Expected: receipt.matching_output_rows equals `7`
   - Expected: receipt.blocked_rows equals `0`
   - Expected: receipt.failed_rows equals `0`
   - Expected: receipt.rejected_rows equals `0`
   - Expected: receipt.fixture_admitted_rows equals `7`
   - Expected: receipt.artifact_admitted_rows equals `7`
   - Expected: receipt.executed_rows equals `7`
   - Expected: receipt.public_wire_bytes equals `2336`
   - Expected: receipt.row_set_sha256.len() equals `64`
   - Expected: reordered.row_set_sha256 equals `receipt.row_set_sha256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit synthetic branch-test rows with typed public receipts")
val receipt = x25519_mlkem768_admit_full_backend_matrix(
    _complete_matrix())
expect(receipt.status).to_equal(X25519MlKem768EvidenceStatus.Pass)
expect(receipt.admitted_rows).to_equal(7)
expect(receipt.matching_output_rows).to_equal(7)
expect(receipt.blocked_rows).to_equal(0)
expect(receipt.failed_rows).to_equal(0)
expect(receipt.rejected_rows).to_equal(0)
expect(receipt.fixture_admitted_rows).to_equal(7)
expect(receipt.artifact_admitted_rows).to_equal(7)
expect(receipt.executed_rows).to_equal(7)
expect(receipt.public_wire_bytes).to_equal(2336)
expect(receipt.row_set_sha256.len()).to_equal(64)
val rows = _complete_matrix()
val permuted = [rows[6], rows[2], rows[4], rows[0],
    rows[5], rows[1], rows[3]]
val reordered = x25519_mlkem768_admit_full_backend_matrix(permuted)
expect(reordered.row_set_sha256).to_equal(receipt.row_set_sha256)
```

</details>

#### retains simultaneous Vulkan and Metal blockers without scalar outputs

- Retain artifact-admitted Vulkan and requested-only Metal
- var rows =  complete matrix
   - Expected: receipt.status equals `X25519MlKem768EvidenceStatus.Blocked`
   - Expected: receipt.admitted_rows equals `5`
   - Expected: receipt.blocked_rows equals `2`
   - Expected: receipt.matching_output_rows equals `5`
   - Expected: receipt.rows[6].source.client_share_sha256 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retain artifact-admitted Vulkan and requested-only Metal")
var rows = _complete_matrix()
rows[5] = _blocked_row(X25519MlKem768EvidenceBackend.Vulkan,
    X25519MlKem768MatrixAdmissionPhase.ArtifactAdmitted,
    "vulkan-runtime-device-capability-binding-unavailable")
rows[6] = _blocked_row(X25519MlKem768EvidenceBackend.Metal,
    X25519MlKem768MatrixAdmissionPhase.Requested,
    "metal-binary-digest-not-pinned-by-fixture-manifest")
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.status).to_equal(X25519MlKem768EvidenceStatus.Blocked)
expect(receipt.admitted_rows).to_equal(5)
expect(receipt.blocked_rows).to_equal(2)
expect(receipt.matching_output_rows).to_equal(5)
expect(receipt.rows[5].source_reason).to_equal(
    "vulkan-runtime-device-capability-binding-unavailable")
expect(receipt.rows[6].source_reason).to_equal(
    "metal-binary-digest-not-pinned-by-fixture-manifest")
expect(receipt.rows[5].output_comparison).to_equal(
    X25519MlKem768MatrixOutputComparison.NotAvailable)
expect(receipt.rows[6].source.client_share_sha256).to_equal("")
val rendered = x25519_mlkem768_render_matrix_receipt(receipt)
expect(rendered).to_contain(
    "row.vulkan.outcome=blocked")
expect(rendered).to_contain(
    "row.metal.outcome=blocked")
expect(rendered).to_contain(
    "row.metal.client_share_sha256=\n")
```

</details>

#### rejects requested-only rows that smuggle fixture or output claims

- Mutate requested-only Metal with an unadmitted public digest
- var rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mutate requested-only Metal with an unadmitted public digest")
var rows = _complete_matrix()
var metal = _blocked_row(X25519MlKem768EvidenceBackend.Metal,
    X25519MlKem768MatrixAdmissionPhase.Requested,
    "metal-binary-digest-not-pinned-by-fixture-manifest")
metal.client_share_sha256 = "d" * 64
rows[6] = metal
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.rows[6].outcome).to_equal(
    X25519MlKem768MatrixRowOutcome.Rejected)
expect(receipt.rows[6].admission_reason).to_equal(
    "requested-row-carries-unadmitted-claims")
```

</details>

#### rejects output and vector-proof claims before execution

- Attach public Set A to fixture-admitted AVX2
- var fixture rows =  complete matrix
- fixture only set a = Some
- Attach RVV execution proof to artifact-admitted RVV
- var artifact rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attach public Set A to fixture-admitted AVX2")
var fixture_rows = _complete_matrix()
var fixture_only = _blocked_row(
    X25519MlKem768EvidenceBackend.Avx2,
    X25519MlKem768MatrixAdmissionPhase.FixtureAdmitted,
    "avx2-runner-artifact-not-admitted")
fixture_only.set_a = Some(_set_a())
fixture_rows[1] = fixture_only
val fixture_receipt = x25519_mlkem768_admit_full_backend_matrix(
    fixture_rows)
expect(fixture_receipt.rows[1].admission_reason).to_equal(
    "fixture-admitted-row-state-invalid")
step("Attach RVV execution proof to artifact-admitted RVV")
var artifact_rows = _complete_matrix()
var artifact_only = _blocked_row(
    X25519MlKem768EvidenceBackend.Rvv,
    X25519MlKem768MatrixAdmissionPhase.ArtifactAdmitted,
    "rvv-native-run-not-started")
artifact_only.execution.observed_rvv_vlen_bits = 256
artifact_rows[3] = artifact_only
val artifact_receipt = x25519_mlkem768_admit_full_backend_matrix(
    artifact_rows)
expect(artifact_receipt.rows[3].admission_reason).to_equal(
    "artifact-admitted-row-state-invalid")
```

</details>

#### binds runner source and rejects malformed artifact provenance

- Change the NEON runner source under an otherwise matching row
- var mismatch rows =  complete matrix
- Reject uppercase non-canonical CUDA runner artifact SHA-256
- var malformed rows =  complete matrix
   - Expected: malformed.artifact_admitted_rows equals `6`
   - Expected: malformed.executed_rows equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the NEON runner source under an otherwise matching row")
var mismatch_rows = _complete_matrix()
mismatch_rows[2].execution.runner_source_sha256 = "8" * 64
val mismatch = x25519_mlkem768_admit_full_backend_matrix(mismatch_rows)
expect(mismatch.rows[2].admission_reason).to_equal(
    "fixture-or-configuration-mismatch")
step("Reject uppercase non-canonical CUDA runner artifact SHA-256")
var malformed_rows = _complete_matrix()
malformed_rows[4].runner_artifact_sha256 = "A" * 64
val malformed = x25519_mlkem768_admit_full_backend_matrix(
    malformed_rows)
expect(malformed.rows[4].admission_reason).to_equal(
    "artifact-provenance-sha256-invalid")
expect(malformed.artifact_admitted_rows).to_equal(6)
expect(malformed.executed_rows).to_equal(6)
```

</details>

#### marks only the independently mutated public Set row mismatched

- Change RVV Set B while preserving its internal typed shape
- var rows =  complete matrix
- var changed b =  set b
- rows[3] set b = Some
   - Expected: receipt.matching_output_rows equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change RVV Set B while preserving its internal typed shape")
var rows = _complete_matrix()
var changed_b = _set_b()
changed_b.first_output_sha256 = "8" * 64
rows[3].set_b = Some(changed_b)
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.rows[3].outcome).to_equal(
    X25519MlKem768MatrixRowOutcome.Rejected)
expect(receipt.rows[3].output_comparison).to_equal(
    X25519MlKem768MatrixOutputComparison.Mismatch)
expect(receipt.rows[2].outcome).to_equal(
    X25519MlKem768MatrixRowOutcome.Admitted)
expect(receipt.matching_output_rows).to_equal(6)
```

</details>

#### keeps execution failures and QEMU rejections as separate rows

- Retain CUDA failure while independently rejecting emulated NEON
- var rows =  complete matrix
   - Expected: receipt.status equals `X25519MlKem768EvidenceStatus.Fail`
   - Expected: receipt.failed_rows equals `1`
   - Expected: receipt.rejected_rows equals `1`
   - Expected: receipt.rows[4].source_reason equals `cuda-device-lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retain CUDA failure while independently rejecting emulated NEON")
var rows = _complete_matrix()
rows[2].execution.mode = X25519MlKem768EvidenceMode.QemuCorrectness
rows[2].execution.emulated = true
rows[4].execution.status = X25519MlKem768EvidenceStatus.Fail
rows[4].execution.reason = "cuda-device-lost"
rows[4].execution.promotion_eligible = false
rows[4].pinned_workload_schema = ""
rows[4].pinned_oracle_id = ""
rows[4].set_a = nil
rows[4].set_b = nil
rows[4].set_c = nil
rows[4].public_wire_bytes = 0
rows[4].client_share_sha256 = ""
rows[4].server_share_sha256 = ""
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.status).to_equal(X25519MlKem768EvidenceStatus.Fail)
expect(receipt.failed_rows).to_equal(1)
expect(receipt.rejected_rows).to_equal(1)
expect(receipt.rows[2].admission_reason).to_equal(
    "native-execution-missing")
expect(receipt.rows[4].source_reason).to_equal("cuda-device-lost")
```

</details>

#### does not classify an unstarted declared failure as executed

- Remove CUDA selection and submission from a declared failure
- var rows =  complete matrix
   - Expected: receipt.executed_rows equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove CUDA selection and submission from a declared failure")
var rows = _complete_matrix()
rows[4].execution.status = X25519MlKem768EvidenceStatus.Fail
rows[4].execution.reason = "cuda-device-lost"
rows[4].execution.promotion_eligible = false
rows[4].execution.selected_backend = nil
rows[4].execution.submitted = false
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.rows[4].outcome).to_equal(
    X25519MlKem768MatrixRowOutcome.Rejected)
expect(receipt.rows[4].admission_reason).to_equal(
    "fallback-or-selection-mismatch")
expect(receipt.executed_rows).to_equal(6)
```

</details>

#### rejects newline injection and impossible backend host identity

- Inject a second rendered key through the Vulkan reason
- var injected rows =  complete matrix
- Claim native NEON execution on x86-64
- var host rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inject a second rendered key through the Vulkan reason")
var injected_rows = _complete_matrix()
injected_rows[5].execution.reason = "pass\nstatus=pass"
val injected = x25519_mlkem768_admit_full_backend_matrix(injected_rows)
expect(injected.rows[5].admission_reason).to_equal(
    "receipt-text-field-invalid")
step("Claim native NEON execution on x86-64")
var host_rows = _complete_matrix()
host_rows[2].host_arch = "x86_64"
val host = x25519_mlkem768_admit_full_backend_matrix(host_rows)
expect(host.rows[2].admission_reason).to_equal(
    "neon-host-architecture-mismatch")
```

</details>

#### changes canonical hash on evidence mutation and redacts secret digests

- Bind device identity and source reason into canonical row material
-  complete matrix
- var rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bind device identity and source reason into canonical row material")
val baseline = x25519_mlkem768_admit_full_backend_matrix(
    _complete_matrix())
var rows = _complete_matrix()
rows[4].execution.device_identity = "different-physical-device"
val changed = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(changed.row_set_sha256 == baseline.row_set_sha256).to_be(false)
val rendered = x25519_mlkem768_render_matrix_receipt(changed)
expect(rendered.contains("shared_secret_sha256")).to_be(false)
expect(rendered.contains("mlkem_shared_sha256")).to_be(false)
```

</details>

#### rejects seven mutually agreeing rows when the scalar oracle is fabricated

- Replace canonical Set A in every row with one shared fake digest
- var rows =  complete matrix
- var fabricated =  set a
- rows[index] set a = Some
   - Expected: receipt.status equals `X25519MlKem768EvidenceStatus.Blocked`
   - Expected: receipt.admitted_rows equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace canonical Set A in every row with one shared fake digest")
var rows = _complete_matrix()
var index: i64 = 0
while index < rows.len():
    var fabricated = _set_a()
    fabricated.first_output_sha256 = "7" * 64
    rows[index].set_a = Some(fabricated)
    index = index + 1
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.status).to_equal(X25519MlKem768EvidenceStatus.Blocked)
expect(receipt.rows[0].admission_reason).to_equal(
    "set-a-set-public-output-oracle-mismatch")
expect(receipt.admitted_rows).to_equal(0)
```

</details>

#### rejects semantic label drift even when public lengths and hashes match

- Change the AVX2 Set B output label only
- var rows =  complete matrix
- var changed b =  set b
- rows[1] set b = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the AVX2 Set B output label only")
var rows = _complete_matrix()
var changed_b = _set_b()
changed_b.first_output_label = "unbound-public-value"
rows[1].set_b = Some(changed_b)
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.rows[1].outcome).to_equal(
    X25519MlKem768MatrixRowOutcome.Rejected)
expect(receipt.rows[1].admission_reason).to_equal(
    "set-b-set-public-output-label-mismatch")
```

</details>

#### retains valid fixture-only and artifact-only blocked phases

- Retain AVX2 after fixture admission but before artifact admission
- var fixture rows =  complete matrix
   - Expected: fixture.fixture_admitted_rows equals `7`
   - Expected: fixture.artifact_admitted_rows equals `6`
- Retain Vulkan after artifact admission but before execution
- var artifact rows =  complete matrix
   - Expected: artifact.artifact_admitted_rows equals `7`
   - Expected: artifact.executed_rows equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retain AVX2 after fixture admission but before artifact admission")
var fixture_rows = _complete_matrix()
fixture_rows[1] = _blocked_row(
    X25519MlKem768EvidenceBackend.Avx2,
    X25519MlKem768MatrixAdmissionPhase.FixtureAdmitted,
    "avx2-runner-artifact-not-admitted")
val fixture = x25519_mlkem768_admit_full_backend_matrix(fixture_rows)
expect(fixture.rows[1].outcome).to_equal(
    X25519MlKem768MatrixRowOutcome.Blocked)
expect(fixture.fixture_admitted_rows).to_equal(7)
expect(fixture.artifact_admitted_rows).to_equal(6)
step("Retain Vulkan after artifact admission but before execution")
var artifact_rows = _complete_matrix()
artifact_rows[5] = _blocked_row(
    X25519MlKem768EvidenceBackend.Vulkan,
    X25519MlKem768MatrixAdmissionPhase.ArtifactAdmitted,
    "vulkan-device-not-opened")
val artifact = x25519_mlkem768_admit_full_backend_matrix(artifact_rows)
expect(artifact.rows[5].outcome).to_equal(
    X25519MlKem768MatrixRowOutcome.Blocked)
expect(artifact.artifact_admitted_rows).to_equal(7)
expect(artifact.executed_rows).to_equal(6)
```

</details>

#### rejects execution contract, fixture, scope, and selection drift

- Reject one row whose implementation version drifts from scalar
- var version rows =  complete matrix
- Reject a matrix consistently using a superseded version
- var legacy rows =  complete matrix
- Reject a noncanonical pinned fixture shared by every row
- var fixture rows =  complete matrix
- Reject a correctness-only CUDA row
- var scope rows =  complete matrix
   - Expected: scoped.rows[4].admission_reason equals `kernel-only-row`
- Reject a selected backend that differs from the request
- var selection rows =  complete matrix
- Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject one row whose implementation version drifts from scalar")
var version_rows = _complete_matrix()
version_rows[1].execution.implementation_version = "0.1.0"
val versioned = x25519_mlkem768_admit_full_backend_matrix(version_rows)
expect(versioned.rows[1].admission_reason).to_equal(
    "fixture-or-configuration-mismatch")
step("Reject a matrix consistently using a superseded version")
var legacy_rows = _complete_matrix()
var legacy_index: i64 = 0
while legacy_index < legacy_rows.len():
    legacy_rows[legacy_index].execution.implementation_version = "0.1.0"
    legacy_index = legacy_index + 1
val legacy = x25519_mlkem768_admit_full_backend_matrix(legacy_rows)
expect(legacy.rows[0].admission_reason).to_equal(
    "execution-contract-version-mismatch")
step("Reject a noncanonical pinned fixture shared by every row")
var fixture_rows = _complete_matrix()
var fixture_index: i64 = 0
while fixture_index < fixture_rows.len():
    fixture_rows[fixture_index].execution.fixture_id = "other-fixture"
    fixture_index = fixture_index + 1
val fixture = x25519_mlkem768_admit_full_backend_matrix(fixture_rows)
expect(fixture.rows[0].admission_reason).to_equal(
    "pinned-fixture-or-batch-mismatch")
step("Reject a correctness-only CUDA row")
var scope_rows = _complete_matrix()
scope_rows[4].execution.scope =
    X25519MlKem768EvidenceScope.Correctness
val scoped = x25519_mlkem768_admit_full_backend_matrix(scope_rows)
expect(scoped.rows[4].admission_reason).to_equal("kernel-only-row")
step("Reject a selected backend that differs from the request")
var selection_rows = _complete_matrix()
selection_rows[5].execution.selected_backend =
    Some(X25519MlKem768EvidenceBackend.ScalarCpu)
val selected = x25519_mlkem768_admit_full_backend_matrix(selection_rows)
expect(selected.rows[5].admission_reason).to_equal(
    "fallback-or-selection-mismatch")
```

</details>

#### requires ISA and GPU execution-start proof before counting execution

- Reject missing RVV vector-length evidence
- var rvv rows =  complete matrix
- Reject RVV-only evidence attached to AVX2
- var avx rows =  complete matrix
- Reject SIMD rows without a vector chunk
- var neon rows =  complete matrix
- Reject CUDA before submission
- var cuda rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject missing RVV vector-length evidence")
var rvv_rows = _complete_matrix()
rvv_rows[3].execution.observed_rvv_vlen_bits = 0
val rvv = x25519_mlkem768_admit_full_backend_matrix(rvv_rows)
expect(rvv.rows[3].admission_reason).to_equal(
    "rvv-vector-length-proof-incomplete")
step("Reject RVV-only evidence attached to AVX2")
var avx_rows = _complete_matrix()
avx_rows[1].execution.observed_rvv_vlen_bits = 256
val avx = x25519_mlkem768_admit_full_backend_matrix(avx_rows)
expect(avx.rows[1].admission_reason).to_equal(
    "non-rvv-row-carries-rvv-proof")
step("Reject SIMD rows without a vector chunk")
var neon_rows = _complete_matrix()
neon_rows[2].execution.simd_chunk_hits = 0
val neon = x25519_mlkem768_admit_full_backend_matrix(neon_rows)
expect(neon.rows[2].admission_reason).to_equal(
    "simd-execution-proof-incomplete")
step("Reject CUDA before submission")
var cuda_rows = _complete_matrix()
cuda_rows[4].execution.submitted = false
val cuda = x25519_mlkem768_admit_full_backend_matrix(cuda_rows)
expect(cuda.rows[4].admission_reason).to_equal(
    "gpu-execution-start-proof-incomplete")
```

</details>

#### requires completed GPU lifecycle and full public output proof

- Reject Vulkan without device readback
- var readback rows =  complete matrix
- Reject fewer than three full-operation kernel invocations
- var kernel rows =  complete matrix
- Reject missing absolute-oracle proof
- var oracle rows =  complete matrix
- Reject incorrect hybrid public shape
- var shape rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject Vulkan without device readback")
var readback_rows = _complete_matrix()
readback_rows[5].execution.device_readback = false
val readback = x25519_mlkem768_admit_full_backend_matrix(readback_rows)
expect(readback.rows[5].admission_reason).to_equal(
    "gpu-device-proof-incomplete")
step("Reject fewer than three full-operation kernel invocations")
var kernel_rows = _complete_matrix()
kernel_rows[4].execution.kernel_invocations = 2
val kernels = x25519_mlkem768_admit_full_backend_matrix(kernel_rows)
expect(kernels.rows[4].admission_reason).to_equal(
    "gpu-device-proof-incomplete")
step("Reject missing absolute-oracle proof")
var oracle_rows = _complete_matrix()
oracle_rows[1].execution.absolute_oracle_match = false
val oracle = x25519_mlkem768_admit_full_backend_matrix(oracle_rows)
expect(oracle.rows[1].admission_reason).to_equal(
    "full-output-oracle-missing")
step("Reject incorrect hybrid public shape")
var shape_rows = _complete_matrix()
shape_rows[2].execution.client_share_bytes = 1215
val shape = x25519_mlkem768_admit_full_backend_matrix(shape_rows)
expect(shape.rows[2].admission_reason).to_equal(
    "hybrid-output-shape-mismatch")
```

</details>

#### rejects incomplete pinned public receipt identities and bindings

- Reject missing Set A
- var missing rows =  complete matrix
- Reject wrong Set C identity
- var identity rows =  complete matrix
- var wrong c =  set c
- identity rows[2] set c = Some
- Reject noncanonical Set A public length
- var length rows =  complete matrix
- var short a =  set a
- length rows[3] set a = Some
- Reject Set C not bound to the row public digest
- var binding rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject missing Set A")
var missing_rows = _complete_matrix()
missing_rows[1].set_a = nil
val missing = x25519_mlkem768_admit_full_backend_matrix(missing_rows)
expect(missing.rows[1].admission_reason).to_equal(
    "missing-set-a-receipt")
step("Reject wrong Set C identity")
var identity_rows = _complete_matrix()
var wrong_c = _set_c()
wrong_c.set_id = X25519MlKem768PinnedSet.X25519
identity_rows[2].set_c = Some(wrong_c)
val identity = x25519_mlkem768_admit_full_backend_matrix(identity_rows)
expect(identity.rows[2].admission_reason).to_equal(
    "set-c-set-identity-mismatch")
step("Reject noncanonical Set A public length")
var length_rows = _complete_matrix()
var short_a = _set_a()
short_a.first_output_bytes = 1183
length_rows[3].set_a = Some(short_a)
val length = x25519_mlkem768_admit_full_backend_matrix(length_rows)
expect(length.rows[3].admission_reason).to_equal(
    "set-a-set-public-output-length-mismatch")
step("Reject Set C not bound to the row public digest")
var binding_rows = _complete_matrix()
binding_rows[4].client_share_sha256 = "7" * 64
val binding = x25519_mlkem768_admit_full_backend_matrix(binding_rows)
expect(binding.rows[4].admission_reason).to_equal(
    "set-c-public-wire-sha256-mismatch")
```

</details>

#### propagates scalar rejection without admitting dependent rows

- Remove scalar promotion eligibility
- var rows =  complete matrix
   - Expected: receipt.admitted_rows equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Remove scalar promotion eligibility")
var rows = _complete_matrix()
rows[0].execution.promotion_eligible = false
val receipt = x25519_mlkem768_admit_full_backend_matrix(rows)
expect(receipt.rows[0].admission_reason).to_equal(
    "row-not-promotion-eligible")
expect(receipt.rows[1].admission_reason).to_equal(
    "scalar-reference-not-admitted")
expect(receipt.admitted_rows).to_equal(0)
```

</details>

#### rejects every impossible backend and host pairing

- Reject AVX2 on AArch64
- var avx rows =  complete matrix
- Reject RVV on x86-64
- var rvv rows =  complete matrix
- Reject Metal outside macOS
- var metal rows =  complete matrix
- Reject an unsupported but syntactically valid OS
- var unknown rows =  complete matrix
- Reject an empty host identity
- var empty rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject AVX2 on AArch64")
var avx_rows = _complete_matrix()
avx_rows[1].host_arch = "aarch64"
val avx = x25519_mlkem768_admit_full_backend_matrix(avx_rows)
expect(avx.rows[1].admission_reason).to_equal(
    "avx2-host-architecture-mismatch")
step("Reject RVV on x86-64")
var rvv_rows = _complete_matrix()
rvv_rows[3].host_arch = "x86_64"
val rvv = x25519_mlkem768_admit_full_backend_matrix(rvv_rows)
expect(rvv.rows[3].admission_reason).to_equal(
    "rvv-host-architecture-mismatch")
step("Reject Metal outside macOS")
var metal_rows = _complete_matrix()
metal_rows[6].host_os = "linux"
val metal = x25519_mlkem768_admit_full_backend_matrix(metal_rows)
expect(metal.rows[6].admission_reason).to_equal(
    "metal-host-os-mismatch")
step("Reject an unsupported but syntactically valid OS")
var unknown_rows = _complete_matrix()
unknown_rows[0].host_os = "plan9"
val unknown = x25519_mlkem768_admit_full_backend_matrix(unknown_rows)
expect(unknown.rows[0].admission_reason).to_equal(
    "unsupported-host-identity")
step("Reject an empty host identity")
var empty_rows = _complete_matrix()
empty_rows[0].host_arch = ""
val empty = x25519_mlkem768_admit_full_backend_matrix(empty_rows)
expect(empty.rows[0].admission_reason).to_equal(
    "host-identity-invalid")
```

</details>

#### rejects invalid requested, provenance, blocked, and failed states

- Reject requested-only execution selection
- var requested rows =  complete matrix
- Some
- Reject malformed fixture provenance
- var provenance rows =  complete matrix
- Reject Blocked status after execution
- var blocked rows =  complete matrix
- Reject failed execution carrying passing public claims
- var failed rows =  complete matrix
- Reject execution against a different admitted artifact
- var artifact rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject requested-only execution selection")
var requested_rows = _complete_matrix()
var requested = _blocked_row(
    X25519MlKem768EvidenceBackend.Metal,
    X25519MlKem768MatrixAdmissionPhase.Requested,
    "metal-binary-unavailable")
requested.execution.selected_backend =
    Some(X25519MlKem768EvidenceBackend.Metal)
requested_rows[6] = requested
val requested_receipt = x25519_mlkem768_admit_full_backend_matrix(
    requested_rows)
expect(requested_receipt.rows[6].admission_reason).to_equal(
    "requested-row-state-invalid")
step("Reject malformed fixture provenance")
var provenance_rows = _complete_matrix()
provenance_rows[1].execution.fixture_manifest_sha256 = "A" * 64
val provenance = x25519_mlkem768_admit_full_backend_matrix(
    provenance_rows)
expect(provenance.rows[1].admission_reason).to_equal(
    "fixture-provenance-sha256-invalid")
step("Reject Blocked status after execution")
var blocked_rows = _complete_matrix()
blocked_rows[4].execution.status =
    X25519MlKem768EvidenceStatus.Blocked
val blocked = x25519_mlkem768_admit_full_backend_matrix(blocked_rows)
expect(blocked.rows[4].admission_reason).to_equal(
    "executed-row-cannot-be-blocked")
step("Reject failed execution carrying passing public claims")
var failed_rows = _complete_matrix()
failed_rows[4].execution.status = X25519MlKem768EvidenceStatus.Fail
failed_rows[4].execution.promotion_eligible = false
val failed = x25519_mlkem768_admit_full_backend_matrix(failed_rows)
expect(failed.rows[4].admission_reason).to_equal(
    "failed-row-state-invalid")
step("Reject execution against a different admitted artifact")
var artifact_rows = _complete_matrix()
artifact_rows[1].execution.artifact_sha256 = "8" * 64
val artifact = x25519_mlkem768_admit_full_backend_matrix(artifact_rows)
expect(artifact.rows[1].admission_reason).to_equal(
    "executed-artifact-binding-mismatch")
```

</details>

#### rejects pinned schema, oracle, public wire, and receipt digest drift

- Reject the wrong pinned workload schema
- var schema rows =  complete matrix
- Reject the wrong pinned oracle identity
- var oracle rows =  complete matrix
- Reject the wrong total public wire length
- var length rows =  complete matrix
- Reject malformed public wire SHA-256
- var public hash rows =  complete matrix
- Reject malformed public execution digest
- var receipt hash rows =  complete matrix


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject the wrong pinned workload schema")
var schema_rows = _complete_matrix()
schema_rows[1].pinned_workload_schema = "pinned-v2"
val schema = x25519_mlkem768_admit_full_backend_matrix(schema_rows)
expect(schema.rows[1].admission_reason).to_equal(
    "pinned-workload-schema-mismatch")
step("Reject the wrong pinned oracle identity")
var oracle_rows = _complete_matrix()
oracle_rows[2].pinned_oracle_id = "scalar-only"
val oracle = x25519_mlkem768_admit_full_backend_matrix(oracle_rows)
expect(oracle.rows[2].admission_reason).to_equal(
    "pinned-oracle-identity-mismatch")
step("Reject the wrong total public wire length")
var length_rows = _complete_matrix()
length_rows[3].public_wire_bytes = 2335
val length = x25519_mlkem768_admit_full_backend_matrix(length_rows)
expect(length.rows[3].admission_reason).to_equal(
    "public-wire-length-mismatch")
step("Reject malformed public wire SHA-256")
var public_hash_rows = _complete_matrix()
public_hash_rows[4].client_share_sha256 = "A" * 64
val public_hash = x25519_mlkem768_admit_full_backend_matrix(
    public_hash_rows)
expect(public_hash.rows[4].admission_reason).to_equal(
    "public-wire-sha256-invalid")
step("Reject malformed public execution digest")
var receipt_hash_rows = _complete_matrix()
receipt_hash_rows[5].execution.keygen_output_digest = "A" * 64
val receipt_hash = x25519_mlkem768_admit_full_backend_matrix(
    receipt_hash_rows)
expect(receipt_hash.rows[5].admission_reason).to_equal(
    "receipt-public-output-digest-invalid")
```

</details>

#### rejects missing or malformed typed Set receipts

- Reject missing Set B
- var missing b rows =  complete matrix
- Reject missing Set C
- var missing c rows =  complete matrix
- Reject malformed Set A public SHA-256
- var hash rows =  complete matrix
- var bad a =  set a
- hash rows[3] set a = Some
- Reject wrong Set B recovered-secret length metadata
- var secret length rows =  complete matrix
- var bad b =  set b
- secret length rows[4] set b = Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject missing Set B")
var missing_b_rows = _complete_matrix()
missing_b_rows[1].set_b = nil
val missing_b = x25519_mlkem768_admit_full_backend_matrix(
    missing_b_rows)
expect(missing_b.rows[1].admission_reason).to_equal(
    "missing-set-b-receipt")
step("Reject missing Set C")
var missing_c_rows = _complete_matrix()
missing_c_rows[2].set_c = nil
val missing_c = x25519_mlkem768_admit_full_backend_matrix(
    missing_c_rows)
expect(missing_c.rows[2].admission_reason).to_equal(
    "missing-set-c-receipt")
step("Reject malformed Set A public SHA-256")
var hash_rows = _complete_matrix()
var bad_a = _set_a()
bad_a.first_output_sha256 = "A" * 64
hash_rows[3].set_a = Some(bad_a)
val hash = x25519_mlkem768_admit_full_backend_matrix(hash_rows)
expect(hash.rows[3].admission_reason).to_equal(
    "set-a-set-public-output-sha256-invalid")
step("Reject wrong Set B recovered-secret length metadata")
var secret_length_rows = _complete_matrix()
var bad_b = _set_b()
bad_b.recovered_secret_bytes = 31
secret_length_rows[4].set_b = Some(bad_b)
val secret_length = x25519_mlkem768_admit_full_backend_matrix(
    secret_length_rows)
expect(secret_length.rows[4].admission_reason).to_equal(
    "set-b-set-secret-length-mismatch")
```

</details>

#### rejects incomplete and duplicate backend sets before admission

- var duplicate =  complete matrix
- duplicate[6] =  pass row
   - Expected: repeated.reason equals `duplicate-backend-vulkan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [X25519MlKem768MatrixRow] = []
val absent = x25519_mlkem768_admit_full_backend_matrix(empty)
expect(absent.reason).to_equal("missing-all-backend-rows")
val short = _complete_matrix().slice(0, 6)
val missing = x25519_mlkem768_admit_full_backend_matrix(short)
expect(missing.reason).to_equal("expected-exactly-seven-backend-rows")
var duplicate = _complete_matrix()
duplicate[6] = _pass_row(X25519MlKem768EvidenceBackend.Vulkan)
val repeated = x25519_mlkem768_admit_full_backend_matrix(duplicate)
expect(repeated.reason).to_equal("duplicate-backend-vulkan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/x25519mlkem768_matrix_receipt_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 backend matrix v2.
- X25519MLKEM768 backend matrix v2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
