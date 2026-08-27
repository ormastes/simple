# Host Gpu Ivshmem Fallback Receipt Specification

> Tests covering Host GPU ivshmem fallback receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Ivshmem Fallback Receipt Specification

## Scenarios

### Host GPU ivshmem fallback receipts

#### accepts a fully valid fallback receipt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a fully valid fallback receipt
   - Expected: accepts(valid_fallback_receipt()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a fully valid fallback receipt")
expect(accepts(valid_fallback_receipt())).to_equal(true)
```

</details>

#### rejects a pass status

- rejects a pass status
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a pass status")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_PASS, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects a zero reason

- rejects a zero reason
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a zero reason")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, 0, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects a nonzero native handle

- rejects a nonzero native handle
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a nonzero native handle")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 1, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects a nonzero device identity

- rejects a nonzero device identity
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a nonzero device identity")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 1, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects device readback source

- rejects device readback source
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects device readback source")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_DEVICE, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects the wrong output byte count

- rejects the wrong output byte count
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the wrong output byte count")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 32, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects a zero output checksum

- rejects a zero output checksum
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a zero output checksum")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 0, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects zero elapsed time

- rejects zero elapsed time
   - Expected: accepts(receipt) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero elapsed time")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(accepts(receipt)).to_equal(false)
```

</details>

#### rejects the wrong generation

- rejects the wrong generation
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the wrong generation")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 8, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
```

</details>

#### rejects the wrong run correlation

- rejects the wrong run correlation
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the wrong run correlation")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 78, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
```

</details>

#### rejects the wrong frame correlation

- rejects the wrong frame correlation
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the wrong frame correlation")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 12, SIMPLEOS_HOST_GPU_BACKEND_CUDA)
expect(host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
```

</details>

#### rejects the wrong backend

- rejects the wrong backend
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the wrong backend")
val receipt = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_SUBMIT_FAILED, 0, 0x1000u64, 64, 12345, 27, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_METAL)
expect(host_gpu_ivshmem_fallback_receipt_valid(receipt, 9, 77, 11, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Host GPU ivshmem fallback receipts.
- Host GPU ivshmem fallback receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64199544dc44b1741fe1be8d7d40f5ec72ea0c9435cd7a6bb0fefca01f5e1d3c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64199544dc44b1741fe1be8d7d40f5ec72ea0c9435cd7a6bb0fefca01f5e1d3c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64199544dc44b1741fe1be8d7d40f5ec72ea0c9435cd7a6bb0fefca01f5e1d3c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.spl
mirror: doc/06_spec/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a fully valid fallback receipt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a pass status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/host_gpu_ivshmem_fallback_receipt_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a zero reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
