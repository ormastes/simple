# Processing Cpu Fallback Policy Contract Specification

> Tests covering SimpleOS processing CPU fallback policy contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Cpu Fallback Policy Contract Specification

## Scenarios

### SimpleOS processing CPU fallback policy contract

#### uses measured backend defaults and preserves explicit overrides

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- query the production offload-threshold resolver for defaults and overrides
   - Expected: simpleos_gpu_processing_min_offload_elements("cuda", -1) equals `536870912`
   - Expected: simpleos_gpu_processing_min_offload_elements("vulkan", -1) equals `65536`
   - Expected: simpleos_gpu_processing_min_offload_elements("metal", -1) equals `536870912`
   - Expected: simpleos_gpu_processing_min_offload_elements("cuda", 0) equals `0`
   - Expected: simpleos_gpu_processing_min_offload_elements("cuda", 123) equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("query the production offload-threshold resolver for defaults and overrides")
expect(simpleos_gpu_processing_min_offload_elements("cuda", -1)).to_equal(536870912)  # oracle: measured CUDA break-even default (512Mi elements)
expect(simpleos_gpu_processing_min_offload_elements("vulkan", -1)).to_equal(65536)  # oracle: measured Vulkan break-even default
expect(simpleos_gpu_processing_min_offload_elements("metal", -1)).to_equal(536870912)  # oracle: measured Metal default matches CUDA class
expect(simpleos_gpu_processing_min_offload_elements("cuda", 0)).to_equal(0)  # oracle: explicit 0 override wins (offload always)
expect(simpleos_gpu_processing_min_offload_elements("cuda", 123)).to_equal(123)  # oracle: explicit positive override wins
```

</details>

#### executes the CPU fallback oracle and it self-verifies

- run the production CPU executor on a FillU32 IR
   - Expected: processing_ir_validate(ir).valid is true
   - Expected: out.len() equals `8`
   - Expected: processing_ir_outputs_equal(out, [0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32]) is true
   - Expected: processing_ir_outputs_equal(out, [0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the production CPU executor on a FillU32 IR")
val ir = processing_ir_fill_u32(8, 0xFF00FF00u32)
expect(processing_ir_validate(ir).valid).to_equal(true)  # oracle: well-formed IR validates
val out = processing_ir_cpu_execute(ir)
expect(out.len()).to_equal(8)  # oracle: one output element per requested element
expect(processing_ir_outputs_equal(out, [0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32, 0xFF00FF00u32])).to_equal(true)  # oracle: exact fill pattern
expect(processing_ir_outputs_equal(out, [0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32])).to_equal(false)  # oracle: mismatch is detected (verify path)
```

</details>

#### the CPU oracle zeroes pixels outside a fill rectangle

- run the CPU executor on a FillRectU32 IR with a strict sub-rectangle
   - Expected: pixels.len() equals `8`
   - Expected: pixels[1] equals `0xABCDu32`
   - Expected: pixels[2] equals `0xABCDu32`
   - Expected: pixels[0] equals `0`
   - Expected: pixels[4] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the CPU executor on a FillRectU32 IR with a strict sub-rectangle")
val rect = processing_ir_fill_rect_u32(4, 2, 4, 1, 0, 2, 1, 0xABCDu32)
val pixels = processing_ir_cpu_execute(rect)
expect(pixels.len()).to_equal(8)  # oracle: stride*height elements
expect(pixels[1]).to_equal(0xABCDu32)  # oracle: row 0, col 1 is inside the rect
expect(pixels[2]).to_equal(0xABCDu32)  # oracle: row 0, col 2 is inside the rect
expect(pixels[0]).to_equal(0)  # oracle: row 0, col 0 is outside the rect
expect(pixels[4]).to_equal(0)  # oracle: row 1 is untouched (rect height 1)
```

</details>

#### the CPU oracle rejects an invalid IR instead of guessing

- execute a hand-built IR with a bad element count
   - Expected: processing_ir_validate(bad).valid is false
   - Expected: processing_ir_cpu_execute(bad) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute a hand-built IR with a bad element count")
val bad = processing_ir_fill_u32(0, 1u32)
expect(processing_ir_validate(bad).valid).to_equal(false)  # oracle: zero-element IR is rejected
expect(processing_ir_cpu_execute(bad)).to_equal([])  # oracle: executor returns empty, never a partial fill
```

</details>

#### keeps fallback wire codes distinct

- read the exported protocol constants
   - Expected: SIMPLEOS_HOST_GPU_STATUS_FALLBACK equals `4`
   - Expected: SIMPLEOS_HOST_GPU_READBACK_CPU equals `2`
   - Expected: SIMPLEOS_HOST_GPU_STATUS_FALLBACK != SIMPLEOS_HOST_GPU_READBACK_CPU is true
   - Expected: SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD equals `18`
   - Expected: SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD != SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read the exported protocol constants")
expect(SIMPLEOS_HOST_GPU_STATUS_FALLBACK).to_equal(4)  # oracle: fallback status wire code
expect(SIMPLEOS_HOST_GPU_READBACK_CPU).to_equal(2)  # oracle: CPU readback source code
expect(SIMPLEOS_HOST_GPU_STATUS_FALLBACK != SIMPLEOS_HOST_GPU_READBACK_CPU).to_equal(true)  # oracle: codes never alias
expect(SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD).to_equal(18)  # oracle: calibrated-break-even reason code
expect(SIMPLEOS_HOST_GPU_REASON_OFFLOAD_OVERHEAD != SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED).to_equal(true)  # oracle: reasons never alias
```

</details>

#### exports a correlated fallback validator and rejects forged provenance

- feed the production validator honest and forged fallback receipts
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(good, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is true
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(wrong_status, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(native_handle, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(wrong_source, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false
   - Expected: host_gpu_ivshmem_fallback_receipt_valid(wrong_correlation, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("feed the production validator honest and forged fallback receipts")
val good = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(good, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(true)  # oracle: honest CPU fallback receipt accepted
val wrong_status = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FAIL, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(wrong_status, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)  # oracle: non-fallback status rejected
val native_handle = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 41, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(native_handle, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)  # oracle: forged native provenance rejected
val wrong_source = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, 1, 31, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(wrong_source, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)  # oracle: non-CPU readback source rejected
val wrong_correlation = fallback_receipt(SIMPLEOS_HOST_GPU_STATUS_FALLBACK, SIMPLEOS_HOST_GPU_REASON_BACKEND_READBACK_FAILED, 0, 0, SIMPLEOS_HOST_GPU_READBACK_CPU, 0, 5)
expect(host_gpu_ivshmem_fallback_receipt_valid(wrong_correlation, 7, 31, 5, SIMPLEOS_HOST_GPU_BACKEND_CUDA, 64)).to_equal(false)  # oracle: run-id correlation mismatch rejected
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS processing CPU fallback policy contract.
- SimpleOS processing CPU fallback policy contract

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c45953b4f8a456a200d0a67bfe74f9a6f02059f0d53a363571acf7ce5a6db1ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c45953b4f8a456a200d0a67bfe74f9a6f02059f0d53a363571acf7ce5a6db1ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c45953b4f8a456a200d0a67bfe74f9a6f02059f0d53a363571acf7ce5a6db1ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses measured backend defaults and preserves explicit overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the CPU fallback oracle and it self-verifies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/processing_cpu_fallback_policy_contract_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the CPU oracle zeroes pixels outside a fill rectangle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
