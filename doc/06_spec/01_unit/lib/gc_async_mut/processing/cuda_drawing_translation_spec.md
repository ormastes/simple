# cuda_drawing_translation_spec

> Verifies the cuda drawing translation behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_drawing_translation_spec

Verifies the cuda drawing translation behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the cuda drawing translation behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### CUDA drawing-access translation

#### should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL

- Verify: should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL
- Exercise success branches
   - Expected: artifact.valid is true
   - Expected: artifact.reason equals `ok`
   - Expected: artifact.format equals `hlsl`
   - Expected: artifact.entry_point equals `processing_fill_rect_u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-007 REQ-011 REQ-012
step("Verify: should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should route CUDA drawing access through the shared validated Vulkan binary artifact
   - Expected: artifact.target equals `ProcessingBackendTarget.VulkanSpirv`
   - Expected: artifact.valid is true
   - Expected: artifact.reason equals `ok`
   - Expected: artifact.format equals `spirv`
   - Expected: artifact.entry_point equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-007 REQ-011 REQ-012
step("Verify: should route CUDA drawing access through the shared validated Vulkan binary artifact")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should accept a full-canvas rectangle at the exact half-open boundary
- Exercise boundary branches
   - Expected: artifact.valid is true
   - Expected: artifact.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-007 REQ-011 REQ-012
step("Verify: should accept a full-canvas rectangle at the exact half-open boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should reject non-drawing and unsupported destination translations
- Exercise rejection branches
   - Expected: non_drawing.valid is false
   - Expected: non_drawing.reason equals `unsupported-cuda-drawing-op`
   - Expected: lossy.valid is false
   - Expected: lossy.reason equals `unsupported-cuda-drawing-translation-target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-007 REQ-011 REQ-012
step("Verify: should reject non-drawing and unsupported destination translations")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should reject invalid coordinates before producing backend source
   - Expected: artifact.valid is false
   - Expected: artifact.reason equals `drawing-rectangle-out-of-bounds`
   - Expected: artifact.source equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-007 REQ-011 REQ-012
step("Verify: should reject invalid coordinates before producing backend source")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val invalid = processing_ir_fill_rect_u32(4, 4, 4, 3, 3, 2, 2, 7u32)
val artifact = translate_cuda_drawing_access(invalid, ProcessingBackendTarget.DirectXHlsl)
expect(artifact.valid).to_equal(false)
expect(artifact.reason).to_equal("drawing-rectangle-out-of-bounds")
expect(artifact.source).to_equal("")
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e6759cc857ab44d98aeb50b476aa338681d430f61dc13bb3b8fb0bd407711a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e6759cc857ab44d98aeb50b476aa338681d430f61dc13bb3b8fb0bd407711a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e6759cc857ab44d98aeb50b476aa338681d430f61dc13bb3b8fb0bd407711a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve binding zero and row-major half-open pixel semantics in DirectX HLSL' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route CUDA drawing access through the shared validated Vulkan binary artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept a full-canvas rectangle at the exact half-open boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject non-drawing and unsupported destination translations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/processing/cuda_drawing_translation_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject invalid coordinates before producing backend source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
