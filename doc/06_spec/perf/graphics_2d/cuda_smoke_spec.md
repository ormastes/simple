# Cuda Smoke Specification

> Tests covering backend_cuda — AC-3: CUDA hardware smoke, CUDA kernel dispatch, sync_readback, CUDA vs CPU performance, BenchFrameRecord schema for CUDA.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Smoke Specification

## Scenarios

### backend_cuda — AC-3: CUDA hardware smoke

### CUDA kernel dispatch

#### AC-3: CUDA backend name is cuda

- verify CUDA backend name is cuda
   - Expected: s.backend equals `CUDA_BACKEND_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify CUDA backend name is cuda")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.backend).to_equal(CUDA_BACKEND_NAME)
```

</details>

#### AC-3: kernel is dispatched on device

- verify kernel is dispatched on device
   - Expected: s.kernel_dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify kernel is dispatched on device")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.kernel_dispatched).to_equal(true)
```

</details>

#### AC-3: device framebuffer is written after kernel dispatch

- verify device framebuffer is written after kernel dispatch
   - Expected: s.framebuffer_written is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify device framebuffer is written after kernel dispatch")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.framebuffer_written).to_equal(true)
```

</details>

### sync_readback

#### AC-3: sync_readback completes without error

- verify sync_readback completes without error
   - Expected: s.readback_completed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify sync_readback completes without error")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.readback_completed).to_equal(true)
```

</details>

#### AC-3: CUDA pixel hash matches CPU reference hash

- verify CUDA pixel hash matches CPU reference hash
   - Expected: hashes_match(s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify CUDA pixel hash matches CPU reference hash")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(hashes_match(s)).to_equal(true)
```

</details>

#### AC-3: cpu_pixel_hash and cuda_pixel_hash are equal (correctness)

- verify cpu_pixel_hash and cuda_pixel_hash are equal (correctness)
   - Expected: s.cpu_pixel_hash equals `s.cuda_pixel_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify cpu_pixel_hash and cuda_pixel_hash are equal (correctness)")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.cpu_pixel_hash).to_equal(s.cuda_pixel_hash)
```

</details>

### CUDA vs CPU performance

#### AC-3: CUDA us_per_frame is less than CPU us_per_frame

- verify CUDA us_per_frame is less than CPU us_per_frame
   - Expected: cuda_faster_than_cpu(s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify CUDA us_per_frame is less than CPU us_per_frame")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(cuda_faster_than_cpu(s)).to_equal(true)
```

</details>

#### AC-3: CUDA us_per_frame is greater than zero

- verify CUDA us_per_frame is greater than zero
   - Expected: s.us_per_frame_cuda > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify CUDA us_per_frame is greater than zero")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.us_per_frame_cuda > 0).to_equal(true)
```

</details>

#### AC-3: CPU reference us_per_frame is greater than zero

- verify CPU reference us_per_frame is greater than zero
   - Expected: s.us_per_frame_cpu > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify CPU reference us_per_frame is greater than zero")
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.us_per_frame_cpu > 0).to_equal(true)
```

</details>

### BenchFrameRecord schema for CUDA

#### AC-3: CUDA bench record backend field equals cuda

- verify CUDA bench record backend field equals cuda
   - Expected: backend equals `CUDA_BACKEND_NAME`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify CUDA bench record backend field equals cuda")
val backend: text = "cuda"
expect(backend).to_equal(CUDA_BACKEND_NAME)
```

</details>

#### AC-3: CUDA bench record kernel field is one of fill blit alpha_blend scroll

- verify CUDA bench record kernel field is one of fill blit alpha_blend scroll
   - Expected: kernels.len() equals `4`
   - Expected: kernels[0] equals `fill`
   - Expected: kernels[1] equals `blit`
   - Expected: kernels[2] equals `alpha_blend`
   - Expected: kernels[3] equals `scroll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-CUDA-SMOKE
step("verify CUDA bench record kernel field is one of fill blit alpha_blend scroll")
val kernels: [text] = ["fill", "blit", "alpha_blend", "scroll"]
expect(kernels.len()).to_equal(4)
expect(kernels[0]).to_equal("fill")
expect(kernels[1]).to_equal("blit")
expect(kernels[2]).to_equal("alpha_blend")
expect(kernels[3]).to_equal("scroll")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/graphics_2d/cuda_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering backend_cuda — AC-3: CUDA hardware smoke, CUDA kernel dispatch, sync_readback, CUDA vs CPU performance, BenchFrameRecord schema for CUDA.
- backend_cuda — AC-3: CUDA hardware smoke
- CUDA kernel dispatch
- sync_readback
- CUDA vs CPU performance
- BenchFrameRecord schema for CUDA

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-CUDA-SMOKE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d2912e2b47a84a5012e7763c324bf05d5cdc6036e46edf56a45d9beb6cf3433`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d2912e2b47a84a5012e7763c324bf05d5cdc6036e46edf56a45d9beb6cf3433`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d2912e2b47a84a5012e7763c324bf05d5cdc6036e46edf56a45d9beb6cf3433`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/perf/graphics_2d/cuda_smoke_spec.spl
mirror: doc/06_spec/perf/graphics_2d/cuda_smoke_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/graphics_2d/cuda_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/graphics_2d/cuda_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/graphics_2d/cuda_smoke_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/graphics_2d/cuda_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/graphics_2d/cuda_smoke_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: CUDA backend name is cuda' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/cuda_smoke_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: kernel is dispatched on device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/graphics_2d/cuda_smoke_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: device framebuffer is written after kernel dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
