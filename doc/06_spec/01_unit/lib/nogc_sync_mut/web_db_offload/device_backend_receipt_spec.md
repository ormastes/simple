# device_backend_receipt_spec

> Prove that web/database offload cannot promote caller-supplied timing or a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# device_backend_receipt_spec

Prove that web/database offload cannot promote caller-supplied timing or a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Prove that web/database offload cannot promote caller-supplied timing or a
synthetic handle into production GPU evidence. This is the fast contract suite
for developers extending the shared device backend boundary.

## Scenarios

### web and database GPU device receipts

#### should preflight rejected work before device dispatch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preflight rejected work before device dispatch
   - Expected: small.reason equals `batch-too-small`
   - Expected: stale.reason equals `stale-generation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preflight rejected work before device dispatch")
val backend = gpu_wdb_device_backend(
    "cuda", 4, ["gpu_db_columnar_scan_batch"], true, "physical-cuda")
val small = gpu_wdb_device_batch_preflight(
    gpu_wdb_queue_initial(1), backend,
    GpuWdbWorkKind.DbScanFilterProject,
    16, 4, 4, true, gpu_wdb_default_budget())
val stale = gpu_wdb_device_batch_preflight(
    gpu_wdb_queue_initial(1), backend,
    GpuWdbWorkKind.DbScanFilterProject,
    8192, 2048, 3, true, gpu_wdb_default_budget())
expect(small.accepted).to_be(false)
expect(small.reason).to_equal("batch-too-small")
expect(stale.accepted).to_be(false)
expect(stale.reason).to_equal("stale-generation")
```

</details>

#### should accept exact device-origin completion evidence

- should accept exact device-origin completion evidence
- Create an exact device readback receipt
- Validate every production provenance field
   - Expected: gpu_wdb_device_receipt_reason(receipt) equals `device-receipt-valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should accept exact device-origin completion evidence")
step("Create an exact device readback receipt")
val receipt = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 123456, 0, false)

step("Validate every production provenance field")
expect(gpu_wdb_device_receipt_valid(receipt)).to_be(true)
expect(gpu_wdb_device_receipt_reason(receipt)).to_equal("device-receipt-valid")
```

</details>

#### should reject synthetic handles and CPU mirrors

- should reject synthetic handles and CPU mirrors
- Create receipts without a real handle and with CPU fallback
- Require typed rejection reasons
   - Expected: gpu_wdb_device_receipt_reason(no_handle) equals `backend-handle-missing`
   - Expected: gpu_wdb_device_receipt_reason(cpu_mirror) equals `cpu-fallback-not-device`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject synthetic handles and CPU mirrors")
step("Create receipts without a real handle and with CPU fallback")
val no_handle = gpu_wdb_device_receipt(
    true, 0, 9001, "device_readback", 123456, 123456, 0, false)
val cpu_mirror = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 123456, 0, true)

step("Require typed rejection reasons")
expect(gpu_wdb_device_receipt_valid(no_handle)).to_be(false)
expect(gpu_wdb_device_receipt_reason(no_handle)).to_equal("backend-handle-missing")
expect(gpu_wdb_device_receipt_valid(cpu_mirror)).to_be(false)
expect(gpu_wdb_device_receipt_reason(cpu_mirror)).to_equal("cpu-fallback-not-device")
```

</details>

#### should reject upload-only and mismatched readback evidence

- should reject upload-only and mismatched readback evidence
- Create upload-only and corrupted readback receipts
- Require device-origin readback and exact CPU parity
   - Expected: gpu_wdb_device_receipt_reason(upload_only) equals `device-readback-missing`
   - Expected: gpu_wdb_device_receipt_reason(mismatch) equals `device-readback-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject upload-only and mismatched readback evidence")
step("Create upload-only and corrupted readback receipts")
val upload_only = gpu_wdb_device_receipt(
    true, 73, 9001, "upload_only", 123456, 123456, 0, false)
val mismatch = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 654321, 1, false)

step("Require device-origin readback and exact CPU parity")
expect(gpu_wdb_device_receipt_valid(upload_only)).to_be(false)
expect(gpu_wdb_device_receipt_reason(upload_only)).to_equal("device-readback-missing")
expect(gpu_wdb_device_receipt_valid(mismatch)).to_be(false)
expect(gpu_wdb_device_receipt_reason(mismatch)).to_equal("device-readback-mismatch")
```

</details>

#### should reject incomplete work and missing device identity

- should reject incomplete work and missing device identity
- Create incomplete and anonymous device receipts
- Require completion and stable device provenance
   - Expected: gpu_wdb_device_receipt_reason(incomplete) equals `device-not-completed`
   - Expected: gpu_wdb_device_receipt_reason(anonymous) equals `device-identity-missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject incomplete work and missing device identity")
step("Create incomplete and anonymous device receipts")
val incomplete = gpu_wdb_device_receipt(
    false, 73, 9001, "device_readback", 123456, 123456, 0, false)
val anonymous = gpu_wdb_device_receipt(
    true, 73, 0, "device_readback", 123456, 123456, 0, false)

step("Require completion and stable device provenance")
expect(gpu_wdb_device_receipt_valid(incomplete)).to_be(false)
expect(gpu_wdb_device_receipt_reason(incomplete)).to_equal("device-not-completed")
expect(gpu_wdb_device_receipt_valid(anonymous)).to_be(false)
expect(gpu_wdb_device_receipt_reason(anonymous)).to_equal("device-identity-missing")
```

</details>

#### should reject zero or internally contradictory checksums

- should reject zero or internally contradictory checksums
- Create zero-checksum and hidden-mismatch receipts
- Require a positive oracle and zero mismatch count
   - Expected: gpu_wdb_device_receipt_reason(zero_checksum) equals `expected-checksum-invalid`
   - Expected: gpu_wdb_device_receipt_reason(hidden_mismatch) equals `device-readback-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject zero or internally contradictory checksums")
step("Create zero-checksum and hidden-mismatch receipts")
val zero_checksum = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 0, 0, 0, false)
val hidden_mismatch = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 123456, 2, false)

step("Require a positive oracle and zero mismatch count")
expect(gpu_wdb_device_receipt_valid(zero_checksum)).to_be(false)
expect(gpu_wdb_device_receipt_reason(zero_checksum)).to_equal("expected-checksum-invalid")
expect(gpu_wdb_device_receipt_valid(hidden_mismatch)).to_be(false)
expect(gpu_wdb_device_receipt_reason(hidden_mismatch)).to_equal("device-readback-mismatch")
```

</details>

#### should keep the canonical unavailable receipt non-promotable

- should keep the canonical unavailable receipt non-promotable
- Construct the canonical unavailable receipt
- Require fail-closed default evidence
   - Expected: gpu_wdb_device_receipt_reason(unavailable) equals `device-not-completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep the canonical unavailable receipt non-promotable")
step("Construct the canonical unavailable receipt")
val unavailable = gpu_wdb_device_receipt_unavailable()

step("Require fail-closed default evidence")
expect(gpu_wdb_device_receipt_valid(unavailable)).to_be(false)
expect(gpu_wdb_device_receipt_reason(unavailable)).to_equal("device-not-completed")
```

</details>

#### should reject missing host timing even with an exact device receipt

- should reject missing host timing even with an exact device receipt
- Create an otherwise valid device submission
- Submit without an ordered host interval
- Refuse the production timing claim
   - Expected: result.reason equals `device-host-timing-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject missing host timing even with an exact device receipt")
step("Create an otherwise valid device submission")
val receipt = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 123456, 0, false)
val backend = gpu_wdb_device_backend(
    "cuda", 4, ["gpu_db_columnar_scan_batch"], true, "physical-cuda")

step("Submit without an ordered host interval")
val result = gpu_wdb_run_device_batch(
    gpu_wdb_queue_initial(1), backend,
    GpuWdbWorkKind.DbScanFilterProject,
    8192, 2048, 4, true, gpu_wdb_default_budget(),
    0, 0, 17, "cuda:event", receipt)

step("Refuse the production timing claim")
expect(result.submission.accepted).to_be(true)
expect(result.production_device_claim).to_be(false)
expect(result.evidence.backend_timing_valid).to_be(false)
expect(result.reason).to_equal("device-host-timing-invalid")
```

</details>

#### should reject zero device duration with an ordered host interval

- should reject zero device duration with an ordered host interval
- Create exact readback and an admitted CUDA target
- Submit with host timing but no device duration
- Refuse duration-free production evidence
   - Expected: result.reason equals `device-duration-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject zero device duration with an ordered host interval")
step("Create exact readback and an admitted CUDA target")
val receipt = gpu_wdb_device_receipt(
    true, 73, 9001, "device_readback", 123456, 123456, 0, false)
val backend = gpu_wdb_device_backend(
    "cuda", 4, ["gpu_db_columnar_scan_batch"], true, "physical-cuda")

step("Submit with host timing but no device duration")
val result = gpu_wdb_run_device_batch(
    gpu_wdb_queue_initial(1), backend,
    GpuWdbWorkKind.DbScanFilterProject,
    8192, 2048, 4, true, gpu_wdb_default_budget(),
    100, 140, 0, "cuda:event", receipt)

step("Refuse duration-free production evidence")
expect(result.submission.accepted).to_be(true)
expect(result.production_device_claim).to_be(false)
expect(result.reason).to_equal("device-duration-invalid")
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b7a4ac93ac5a6284fd08b1abcc5d069e9688709fe5773bd9d17dcb616c406cba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b7a4ac93ac5a6284fd08b1abcc5d069e9688709fe5773bd9d17dcb616c406cba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b7a4ac93ac5a6284fd08b1abcc5d069e9688709fe5773bd9d17dcb616c406cba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preflight rejected work before device dispatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preflight rejected work before device dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept exact device-origin completion evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept exact device-origin completion evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject synthetic handles and CPU mirrors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject synthetic handles and CPU mirrors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject upload-only and mismatched readback evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject incomplete work and missing device identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_sync_mut/web_db_offload/device_backend_receipt_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject zero or internally contradictory checksums' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
