# Gpu Runtime Specification

> Tests covering GPU Runtime API, Backend Detection, Tensor Creation, CUDA Transfer, Allocation Helpers, Stream Operations, Multi-GPU.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Runtime Specification

## Scenarios

### GPU Runtime API

### Backend Detection

#### detects if GPU is available

- detects if GPU is available
   - Expected: available == true or available == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects if GPU is available")
val available = gpu_available()
# Should return bool (true or false)
expect(available == true or available == false).to_equal(true)
```

</details>

#### returns backend name

- returns backend name
   - Expected: name == "CUDA" or name == "CPU" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns backend name")
val name = gpu_backend_name()
# Should be "CUDA" or "CPU"
expect(name == "CUDA" or name == "CPU").to_equal(true)
```

</details>

#### returns device count

- returns device count
   - Expected: count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns device count")
# Skipped: Requires PyTorch FFI loaded
val count = gpu_device_count()
expect(count >= 0).to_equal(true)
```

</details>

### Tensor Creation

#### creates zero tensor

- creates zero tensor
   - Expected: handle > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates zero tensor")
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_zeros(10, 10)
expect(handle > 0).to_equal(true)
```

</details>

#### creates ones tensor

- creates ones tensor
   - Expected: handle > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates ones tensor")
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_ones(10, 10)
expect(handle > 0).to_equal(true)
```

</details>

#### reports correct element count

- reports correct element count
   - Expected: count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct element count")
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_zeros(5, 4)
val count = gpu_tensor_numel(handle)
expect(count).to_equal(20)
```

</details>

### CUDA Transfer

#### moves tensor to CUDA

- moves tensor to CUDA
   - Expected: is_cuda is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves tensor to CUDA")
# Skipped: Requires CUDA available
val cpu_handle = gpu_tensor_zeros(10, 10)
val gpu_handle = gpu_tensor_to_cuda(cpu_handle, 0)
val is_cuda = gpu_tensor_is_cuda(gpu_handle)
expect(is_cuda).to_equal(true)
```

</details>

#### detects CPU tensor correctly

- detects CPU tensor correctly
   - Expected: is_cuda is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects CPU tensor correctly")
# Skipped: Requires PyTorch FFI
val handle = gpu_tensor_zeros(10, 10)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(false)
```

</details>

### Allocation Helpers

#### allocates zeros on CPU

- allocates zeros on CPU
   - Expected: is_cuda is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates zeros on CPU")
# Skipped: Requires PyTorch FFI
val handle = gpu_alloc_zeros(10, 10, use_gpu: false, device_id: 0)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(false)
```

</details>

#### allocates zeros on GPU

- allocates zeros on GPU
   - Expected: is_cuda is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates zeros on GPU")
# Skipped: Requires CUDA
val handle = gpu_alloc_zeros(10, 10, use_gpu: true, device_id: 0)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(true)
```

</details>

#### allocates ones on GPU

- allocates ones on GPU
   - Expected: is_cuda is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates ones on GPU")
# Skipped: Requires CUDA
val handle = gpu_alloc_ones(10, 10, use_gpu: true, device_id: 0)
val is_cuda = gpu_tensor_is_cuda(handle)
expect(is_cuda).to_equal(true)
```

</details>

### Stream Operations

#### creates CUDA stream

- creates CUDA stream
   - Expected: stream > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates CUDA stream")
# Skipped: Requires CUDA
val stream = gpu_stream_create(0)
expect(stream > 0).to_equal(true)
```

</details>

#### synchronizes stream

- synchronizes stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("synchronizes stream")
# Skipped: Requires CUDA
val stream = gpu_stream_create(0)
gpu_stream_sync(stream)
# Should complete without error
```

</details>

#### queries stream status

- queries stream status
   - Expected: complete == true or complete == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("queries stream status")
# Skipped: Requires CUDA
val stream = gpu_stream_create(0)
val complete = gpu_stream_query(stream)
expect(complete == true or complete == false).to_equal(true)
```

</details>

### Multi-GPU

#### allocates on different devices

- allocates on different devices
   - Expected: is_cuda_0 is true
   - Expected: is_cuda_1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates on different devices")
# Skipped: Requires multiple GPUs
val gpu0 = gpu_alloc_zeros(10, 10, use_gpu: true, device_id: 0)
val gpu1 = gpu_alloc_zeros(10, 10, use_gpu: true, device_id: 1)

val is_cuda_0 = gpu_tensor_is_cuda(gpu0)
val is_cuda_1 = gpu_tensor_is_cuda(gpu1)

expect(is_cuda_0).to_equal(true)
expect(is_cuda_1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU Runtime API, Backend Detection, Tensor Creation, CUDA Transfer, Allocation Helpers, Stream Operations, Multi-GPU.
- GPU Runtime API
- Backend Detection
- Tensor Creation
- CUDA Transfer
- Allocation Helpers
- Stream Operations
- Multi-GPU

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `f2da460254c344bc3564ec48471a5f0345be6eea43b153aaf7c62d5237afa9df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2da460254c344bc3564ec48471a5f0345be6eea43b153aaf7c62d5237afa9df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2da460254c344bc3564ec48471a5f0345be6eea43b153aaf7c62d5237afa9df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/gc_async_mut/gpu_runtime_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu_runtime_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu_runtime_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/gpu_runtime_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects if GPU is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_runtime_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns backend name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu_runtime_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns device count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
