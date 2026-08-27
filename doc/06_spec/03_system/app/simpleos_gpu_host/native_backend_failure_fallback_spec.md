# native_backend_failure_fallback_spec

> Failure and fallback receipts for the canonical SimpleOS host-GPU protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_backend_failure_fallback_spec

Failure and fallback receipts for the canonical SimpleOS host-GPU protocol.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Failure and fallback receipts for the canonical SimpleOS host-GPU protocol.

This is a checker-level injection suite. The protocol currently has no live
submit/readback fault-injection hook, so these cases inject structured wire
receipts into the production validators rather than claiming hardware proof.

## Scenarios

### SimpleOS host-GPU backend failure and fallback receipts

#### records unavailable CUDA, Vulkan, and Metal without silently selecting another backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records unavailable CUDA, Vulkan, and Metal without silently selecting another backend
   - Expected: simpleos_host_gpu_validate_batch(batch).status equals `pass`
   - Expected: simpleos_host_gpu_validate_receipt(batch, unavailable).status equals `pass`
   - Expected: unavailable.status equals `unsupported`
   - Expected: unavailable.reason equals `backend-unavailable`
   - Expected: batch.backend equals `backend`
   - Expected: unavailable.backend equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records unavailable CUDA, Vulkan, and Metal without silently selecting another backend")
for backend in ["cuda", "vulkan", "metal"]:
    val batch = processing_batch(backend, 10)
    expect(simpleos_host_gpu_validate_batch(batch).status).to_equal("pass")
    val unavailable = receipt(batch, "unsupported", "unavailable", "backend-unavailable", "none", 0, 0, 0)
    expect(simpleos_host_gpu_validate_receipt(batch, unavailable).status).to_equal("pass")
    expect(unavailable.status).to_equal("unsupported")
    expect(unavailable.reason).to_equal("backend-unavailable")
    expect(batch.backend).to_equal(backend)
    expect(unavailable.backend).to_equal("unavailable")
    expect(batch.backend != unavailable.backend).to_be(true)
    val forged = receipt(batch, "unsupported", "unavailable", "backend-unavailable", "device_readback", 41, 17, 64)
    expect(simpleos_host_gpu_validate_receipt(batch, forged).reason).to_equal(
        "dishonest-failure-provenance")
```

</details>

#### rejects an invalid processing request before receipt promotion

- rejects an invalid processing request before receipt promotion
   - Expected: batch_check.ok is false
   - Expected: batch_check.status equals `fail`
   - Expected: batch_check.reason equals `invalid-processing-element-count`
   - Expected: simpleos_host_gpu_validate_receipt(invalid, failed).status equals `pass`
   - Expected: failed.status equals `fail`
   - Expected: failed.backend equals `invalid.backend`
   - Expected: failed.reason equals `invalid-request`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects an invalid processing request before receipt promotion")
val invalid = SimpleOsHostGpuBatch(
    version: SIMPLEOS_HOST_GPU_PROTOCOL_VERSION,
    generation: 11,
    run_id: "invalid-request",
    frame_id: 1,
    kind: "processing",
    backend: "cuda",
    width: 0,
    height: 0,
    element_count: 0,
    payload_bytes: 64,
    payload_checksum: 17
)
val batch_check = simpleos_host_gpu_validate_batch(invalid)
expect(batch_check.ok).to_equal(false)
expect(batch_check.status).to_equal("fail")
expect(batch_check.reason).to_equal("invalid-processing-element-count")
val failed = receipt(invalid, "fail", "cuda", "invalid-request", "none", 0, 0, 0)
expect(simpleos_host_gpu_validate_receipt(invalid, failed).status).to_equal("pass")
expect(failed.status).to_equal("fail")
expect(failed.backend).to_equal(invalid.backend)
expect(failed.reason).to_equal("invalid-request")
```

</details>

#### keeps a submit failure failed and rejects a CPU masquerading as a GPU pass

- keeps a submit failure failed and rejects a CPU masquerading as a GPU pass
   - Expected: simpleos_host_gpu_validate_receipt(batch, submit_failed).status equals `pass`
   - Expected: submit_failed.status equals `fail`
   - Expected: submit_failed.reason equals `submit-failed`
   - Expected: submit_failed.readback_source equals `none`
   - Expected: simpleos_host_gpu_validate_receipt(batch, forged_pass).reason equals `backend-correlation-mismatch`
   - Expected: simpleos_host_gpu_validate_receipt(batch, same_backend_forged_pass).reason equals `non-device-readback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps a submit failure failed and rejects a CPU masquerading as a GPU pass")
val batch = processing_batch("cuda", 12)
val submit_failed = receipt(batch, "fail", "cuda", "submit-failed", "none", 0, 0, 0)
expect(simpleos_host_gpu_validate_receipt(batch, submit_failed).status).to_equal("pass")
expect(submit_failed.status).to_equal("fail")
expect(submit_failed.reason).to_equal("submit-failed")
expect(submit_failed.readback_source).to_equal("none")
val forged_failure = receipt(batch, "fail", "cuda", "submit-failed", "device_readback", 41, 17, 64)
expect(simpleos_host_gpu_validate_receipt(batch, forged_failure).reason).to_equal(
    "dishonest-failure-provenance")
val forged_blocked = receipt(batch, "blocked", "cuda", "driver-reset", "device_readback", 41, 17, 64)
expect(simpleos_host_gpu_validate_receipt(batch, forged_blocked).reason).to_equal(
    "dishonest-failure-provenance")
val forged_pass = receipt(batch, "pass", "cpu", "pass", "cpu_reference", 0, 17, 64)
expect(simpleos_host_gpu_validate_receipt(batch, forged_pass).reason).to_equal("backend-correlation-mismatch")
val same_backend_forged_pass = receipt(batch, "pass", "cuda", "pass", "cpu_reference", 41, 17, 64)
expect(simpleos_host_gpu_validate_receipt(batch, same_backend_forged_pass).reason).to_equal("non-device-readback")
```

</details>

#### fails closed on a readback size or checksum mismatch

- fails closed on a readback size or checksum mismatch
   - Expected: simpleos_host_gpu_validate_receipt(batch, wrong_size).reason equals `output-size-mismatch`
   - Expected: simpleos_host_gpu_validate_receipt(batch, missing_checksum).reason equals `missing-output-checksum`
   - Expected: simpleos_host_gpu_validate_receipt(batch, readback_failed).status equals `pass`
   - Expected: readback_failed.status equals `fail`
   - Expected: readback_failed.reason equals `readback-failed`
   - Expected: simpleos_host_gpu_validate_receipt(batch, checksum_mismatch).status equals `pass`
   - Expected: checksum_mismatch.status equals `fail`
   - Expected: checksum_mismatch.reason equals `checksum-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed on a readback size or checksum mismatch")
val batch = processing_batch("vulkan", 13)
val wrong_size = receipt(batch, "pass", "vulkan", "pass", "device_readback", 41, 17, 4)
expect(simpleos_host_gpu_validate_receipt(batch, wrong_size).reason).to_equal("output-size-mismatch")
val missing_checksum = receipt(batch, "pass", "vulkan", "pass", "device_readback", 41, 0, 64)
expect(simpleos_host_gpu_validate_receipt(batch, missing_checksum).reason).to_equal("missing-output-checksum")
val readback_failed = receipt(batch, "fail", "vulkan", "readback-failed", "none", 0, 0, 0)
expect(simpleos_host_gpu_validate_receipt(batch, readback_failed).status).to_equal("pass")
expect(readback_failed.status).to_equal("fail")
expect(readback_failed.reason).to_equal("readback-failed")
val checksum_mismatch = receipt(batch, "fail", "vulkan", "checksum-mismatch", "none", 0, 0, 0)
expect(simpleos_host_gpu_validate_receipt(batch, checksum_mismatch).status).to_equal("pass")
expect(checksum_mismatch.status).to_equal("fail")
expect(checksum_mismatch.reason).to_equal("checksum-mismatch")
expect(readback_failed.reason != checksum_mismatch.reason).to_be(true)
```

</details>

#### accepts only an explicit CPU fallback receipt and keeps it distinct from the request

- accepts only an explicit CPU fallback receipt and keeps it distinct from the request
   - Expected: simpleos_host_gpu_validate_receipt(batch, fallback).status equals `pass`
   - Expected: fallback.status equals `fallback`
   - Expected: fallback.backend equals `cpu`
   - Expected: fallback.native_handle equals `0`
   - Expected: fallback.readback_source equals `cpu_reference`
   - Expected: forbidden_check.ok is false
   - Expected: forbidden_check.reason equals `backend-correlation-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts only an explicit CPU fallback receipt and keeps it distinct from the request")
for backend in ["cuda", "vulkan", "metal"]:
    val batch = processing_batch(backend, 20)
    val fallback = receipt(batch, "fallback", "cpu", "host-service-unavailable", "cpu_reference", 0, 17, 64)
    expect(simpleos_host_gpu_validate_receipt(batch, fallback).status).to_equal("pass")
    expect(fallback.status).to_equal("fallback")
    expect(fallback.backend).to_equal("cpu")
    expect(batch.backend != fallback.backend).to_be(true)
    expect(fallback.native_handle).to_equal(0)
    expect(fallback.readback_source).to_equal("cpu_reference")
    val forbidden_gpu_pass = receipt(batch, "pass", "cpu", "pass", "cpu_reference", 0, 17, 64)
    val forbidden_check = simpleos_host_gpu_validate_receipt(batch, forbidden_gpu_pass)
    expect(forbidden_check.ok).to_equal(false)
    expect(forbidden_check.reason).to_equal("backend-correlation-mismatch")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `afb91a353a14a48175e8eec7e11a05041578caf16a1859df82d919e970fd26ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afb91a353a14a48175e8eec7e11a05041578caf16a1859df82d919e970fd26ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afb91a353a14a48175e8eec7e11a05041578caf16a1859df82d919e970fd26ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records unavailable CUDA, Vulkan, and Metal without silently selecting another backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an invalid processing request before receipt promotion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/native_backend_failure_fallback_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a submit failure failed and rejects a CPU masquerading as a GPU pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
