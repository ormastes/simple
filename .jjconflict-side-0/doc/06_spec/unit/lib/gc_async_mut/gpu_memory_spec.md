# Gpu Memory Specification

> Tests covering GpuArray, upload, download, copy_to, size_bytes, GPU Allocation Functions, gpu_alloc, gpu_alloc_upload, gpu_alloc_zeros.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Memory Specification

## Scenarios

### GpuArray

### upload

#### uploads data from host to device

- uploads data from host to device
   - Expected: data_len equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uploads data from host to device")
# Creates CPU tensor from data, moves to GPU, stores handle
val data_len = 4
expect(data_len).to_equal(4)
```

</details>

#### updates count after upload

- updates count after upload
   - Expected: count equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates count after upload")
val count = 1024
expect(count).to_equal(1024)
```

</details>

#### returns true on successful upload

- returns true on successful upload
   - Expected: success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true on successful upload")
val success = true
expect(success).to_equal(true)
```

</details>

#### returns false for unsupported backend

- returns false for unsupported backend
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unsupported backend")
val success = false
expect(success).to_equal(false)
```

</details>

### download

#### moves tensor to CPU for download

- moves tensor to CPU for download
   - Expected: downloaded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves tensor to CPU for download")
# rt_torch_torchtensor_cpu then extract data
val downloaded = true
expect(downloaded).to_equal(true)
```

</details>

#### returns empty array when no tensor stored

- returns empty array when no tensor stored
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty array when no tensor stored")
var result = []
expect(result.len()).to_equal(0)
```

</details>

#### returns empty for unsupported backend

- returns empty for unsupported backend
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unsupported backend")
var result = []
expect(result.len()).to_equal(0)
```

</details>

### copy_to

#### clones and transfers to destination device

- clones and transfers to destination device
   - Expected: copied is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clones and transfers to destination device")
# rt_torch_torchtensor_clone then cuda(other.device_id)
val copied = true
expect(copied).to_equal(true)
```

</details>

#### updates destination count

- updates destination count
   - Expected: src_count equals `dst_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates destination count")
val src_count = 100
val dst_count = 100
expect(src_count).to_equal(dst_count)
```

</details>

#### returns false when source has no tensor

- returns false when source has no tensor
   - Expected: success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when source has no tensor")
val success = false
expect(success).to_equal(false)
```

</details>

### size_bytes

#### calculates size using default element size

- calculates size using default element size
   - Expected: expected_bytes equals `8192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates size using default element size")
# count * 8 (default bytes per element)
val count = 1024
val expected_bytes = count * 8
expect(expected_bytes).to_equal(8192)
```

</details>

### GPU Allocation Functions

### gpu_alloc

#### allocates empty GPU array with zeros

- allocates empty GPU array with zeros
   - Expected: count equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates empty GPU array with zeros")
# Creates zeros tensor on CPU, moves to GPU
val count = 512
expect(count).to_equal(512)
```

</details>

#### returns fallback for unsupported backend

- returns fallback for unsupported backend
   - Expected: device_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns fallback for unsupported backend")
val device_id = -1
expect(device_id).to_equal(-1)
```

</details>

### gpu_alloc_upload

#### allocates and uploads in one call

- allocates and uploads in one call
   - Expected: data.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates and uploads in one call")
val data = [1.0, 2.0, 3.0]
expect(data.len()).to_equal(3)
```

</details>

### gpu_alloc_zeros

#### creates zero-initialized GPU array

- creates zero-initialized GPU array
   - Expected: count equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates zero-initialized GPU array")
val count = 256
expect(count).to_equal(256)
```

</details>

#### uses PyTorch zeros tensor

- uses PyTorch zeros tensor
   - Expected: zeros_used is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses PyTorch zeros tensor")
val zeros_used = true
expect(zeros_used).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu_memory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GpuArray, upload, download, copy_to, size_bytes, GPU Allocation Functions, gpu_alloc, gpu_alloc_upload, gpu_alloc_zeros.
- GpuArray
- upload
- download
- copy_to
- size_bytes
- GPU Allocation Functions
- gpu_alloc
- gpu_alloc_upload
- gpu_alloc_zeros

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `2a0c995fa9a42c8df1a333bc5f8458481ca4e1f04949c8f5b3bd6e1fac223db9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a0c995fa9a42c8df1a333bc5f8458481ca4e1f04949c8f5b3bd6e1fac223db9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a0c995fa9a42c8df1a333bc5f8458481ca4e1f04949c8f5b3bd6e1fac223db9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/gc_async_mut/gpu_memory_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu_memory_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu_memory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu_memory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu_memory_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/gpu_memory_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uploads data from host to device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_memory_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates count after upload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_memory_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns true on successful upload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
