# Cuda Drawing Translation Specification

> Tests covering CUDA drawing-access translation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Drawing Translation Specification

## Scenarios

### CUDA drawing-access translation

#### should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL
- Exercise success branches
   - Expected: artifact.valid is true
   - Expected: artifact.reason equals `ok`
   - Expected: artifact.format equals `hlsl`
   - Expected: artifact.entry_point equals `processing_fill_rect_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL")
step("Exercise success branches")
val ir = processing_ir_fill_rect_u32(8, 6, 10, 2, 1, 3, 4, 0xAABBCCDDu32)
val artifact = translate_cuda_drawing_access(ir, ProcessingBackendTarget.DirectXHlsl)
expect(artifact.valid).to_equal(true)
expect(artifact.reason).to_equal("ok")
expect(artifact.format).to_equal("hlsl")
expect(artifact.entry_point).to_equal("processing_fill_rect_u32")
expect(artifact.source).to_contain("RWStructuredBuffer<uint> output : register(u0)")
expect(artifact.source).to_contain("cbuffer DrawParams : register(b0)")
expect(artifact.source).to_contain("px < rect_x + rect_width")
expect(artifact.source).to_contain("py < rect_y + rect_height")
expect(artifact.source).to_contain("output[py * stride + px]")
expect(artifact.source).to_contain("inside ? pixel_value : 0u")
```

</details>

#### should route CUDA drawing access through the shared validated Vulkan binary artifact

- should route CUDA drawing access through the shared validated Vulkan binary artifact
   - Expected: artifact.target equals `ProcessingBackendTarget.VulkanSpirv`
   - Expected: artifact.valid is true
   - Expected: artifact.reason equals `ok`
   - Expected: artifact.format equals `spirv`
   - Expected: artifact.entry_point equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should route CUDA drawing access through the shared validated Vulkan binary artifact")
val ir = processing_ir_fill_rect_u32(8, 6, 8, 1, 2, 4, 3, 7u32)
val artifact = translate_cuda_drawing_access(ir, ProcessingBackendTarget.VulkanSpirv)
expect(artifact.target).to_equal(ProcessingBackendTarget.VulkanSpirv)
expect(artifact.valid).to_equal(true)
expect(artifact.reason).to_equal("ok")
expect(artifact.format).to_equal("spirv")
expect(artifact.entry_point).to_equal("main")
expect(artifact.binary.len()).to_be_greater_than(0)
```

</details>

#### should accept a full-canvas rectangle at the exact half-open boundary

- should accept a full-canvas rectangle at the exact half-open boundary
- Exercise boundary branches
   - Expected: artifact.valid is true
   - Expected: artifact.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should accept a full-canvas rectangle at the exact half-open boundary")
step("Exercise boundary branches")
val ir = processing_ir_fill_rect_u32(4, 3, 4, 0, 0, 4, 3, 0xFFFFFFFFu32)
val artifact = translate_cuda_drawing_access(ir, ProcessingBackendTarget.DirectXHlsl)
expect(artifact.valid).to_equal(true)
expect(artifact.reason).to_equal("ok")
expect(artifact.source).to_contain("px < rect_x + rect_width")
expect(artifact.source).to_contain("py < rect_y + rect_height")
```

</details>

#### should reject non-drawing and unsupported destination translations

- should reject non-drawing and unsupported destination translations
- Exercise rejection branches
   - Expected: non_drawing.valid is false
   - Expected: non_drawing.reason equals `unsupported-cuda-drawing-op`
   - Expected: lossy.valid is false
   - Expected: lossy.reason equals `unsupported-cuda-drawing-translation-target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject non-drawing and unsupported destination translations")
step("Exercise rejection branches")
val fill = processing_ir_fill_u32(64, 7u32)
val non_drawing = translate_cuda_drawing_access(fill, ProcessingBackendTarget.DirectXHlsl)
expect(non_drawing.valid).to_equal(false)
expect(non_drawing.reason).to_equal("unsupported-cuda-drawing-op")
val rect = processing_ir_fill_rect_u32(4, 4, 4, 0, 0, 4, 4, 7u32)
val lossy = translate_cuda_drawing_access(rect, ProcessingBackendTarget.MetalMsl)
expect(lossy.valid).to_equal(false)
expect(lossy.reason).to_equal("unsupported-cuda-drawing-translation-target")
```

</details>

#### should reject invalid coordinates before producing backend source

- should reject invalid coordinates before producing backend source
   - Expected: artifact.valid is false
   - Expected: artifact.reason equals `drawing-rectangle-out-of-bounds`
   - Expected: artifact.source equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject invalid coordinates before producing backend source")
val invalid = processing_ir_fill_rect_u32(4, 4, 4, 3, 3, 2, 2, 7u32)
val artifact = translate_cuda_drawing_access(invalid, ProcessingBackendTarget.DirectXHlsl)
expect(artifact.valid).to_equal(false)
expect(artifact.reason).to_equal("drawing-rectangle-out-of-bounds")
expect(artifact.source).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CUDA drawing-access translation.
- CUDA drawing-access translation

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

- `REQ-SSPEC-UNIT`
- `REQ-006`
- `REQ-007`
- `REQ-011`
- `REQ-012`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `95d93a41c7024cb96a96a1a103eecf0a749f019369099fb6afab26c6de9448ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95d93a41c7024cb96a96a1a103eecf0a749f019369099fb6afab26c6de9448ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95d93a41c7024cb96a96a1a103eecf0a749f019369099fb6afab26c6de9448ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.md (current)
findings: 11 blockers: 1
  narrative=100 structure=75 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:20:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route CUDA drawing access through the shared validated Vulkan binary artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route CUDA drawing access through the shared validated Vulkan binary artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept a full-canvas rectangle at the exact half-open boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept a full-canvas rectangle at the exact half-open boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject non-drawing and unsupported destination translations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid coordinates before producing backend source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
