# Generated Kernel Dispatch Specification

> Tests covering Engine2D generated kernel dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generated Kernel Dispatch Specification

## Scenarios

### Engine2D generated kernel dispatch

#### produces CUDA Vulkan and Metal generated 2D launch plans

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces CUDA Vulkan and Metal generated 2D launch plans
   - Expected: cuda.compute_target equals `cuda`
   - Expected: cuda.binary_format equals `ptx`
   - Expected: cuda.launch_api equals `cuda_launch_api`
   - Expected: cuda.entry_name equals `simple_2d_fill_u32`
   - Expected: vulkan.compute_target equals `vulkan`
   - Expected: vulkan_dispatch.source_format equals `spirv`
   - Expected: vulkan.binary_format equals `spirv`
   - Expected: vulkan.compile_tool equals `vulkan-spirv-runtime`
   - Expected: vulkan.launch_api equals `vkCmdDispatch`
   - Expected: metal.compute_target equals `metal`
   - Expected: metal.binary_format equals `metallib`
   - Expected: metal.launch_api equals `MTLComputeCommandEncoder.dispatchThreads`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces CUDA Vulkan and Metal generated 2D launch plans")
val cuda = generated_2d_launch_plan("cuda", GENERATED_2D_FILL, 64, 64)
val vulkan_dispatch = generated_2d_dispatch_for_backend("vulkan")
val vulkan = generated_2d_launch_plan("vulkan", GENERATED_2D_FILL, 64, 64)
val metal = generated_2d_launch_plan("metal", GENERATED_2D_FILL, 64, 64)

expect(cuda.compute_target).to_equal("cuda")
expect(cuda.binary_format).to_equal("ptx")
expect(cuda.launch_api).to_equal("cuda_launch_api")
expect(cuda.entry_name).to_equal("simple_2d_fill_u32")
expect(vulkan.compute_target).to_equal("vulkan")
expect(vulkan_dispatch.source_format).to_equal("spirv")
expect(vulkan.binary_format).to_equal("spirv")
expect(vulkan.compile_tool).to_equal("vulkan-spirv-runtime")
expect(vulkan.launch_api).to_equal("vkCmdDispatch")
expect(vulkan.required_entries).to_contain("simple_2d_bitmap_glyph_raster_u32")
expect(metal.compute_target).to_equal("metal")
expect(metal.binary_format).to_equal("metallib")
expect(metal.launch_api).to_equal("MTLComputeCommandEncoder.dispatchThreads")
```

</details>

#### requires CUDA Vulkan and Metal artifact load submit and readback proof before device execution

- requires CUDA Vulkan and Metal artifact load submit and readback proof before device execution
   - Expected: cuda_missing_args.reason equals `missing-args-pointer`
   - Expected: cuda_request.handle_kind equals `cuda-kernel-args`
   - Expected: cuda_request.call_shape() equals `cuda_launch_api`
   - Expected: cuda_submit_failed.reason equals `backend-submit-failed`
   - Expected: cuda_no_readback.reason equals `device-readback-required`
   - Expected: cuda_zero_expected.reason equals `expected-checksum-required`
   - Expected: cuda_mismatch.reason equals `device-readback-checksum-mismatch`
   - Expected: cuda_executed.reason equals `readback-checksum-matched`
   - Expected: missing_queue.reason equals `missing-queue-or-encoder-handle`
   - Expected: request.handle_kind equals `vulkan-command-buffer-pipeline`
   - Expected: request.call_shape() equals `vulkan_compute_api`
   - Expected: submit_failed.reason equals `backend-submit-failed`
   - Expected: no_readback.reason equals `device-readback-required`
   - Expected: zero_expected.reason equals `expected-checksum-required`
   - Expected: mismatch.reason equals `device-readback-checksum-mismatch`
   - Expected: executed.reason equals `readback-checksum-matched`
   - Expected: metal_missing_encoder.reason equals `missing-queue-or-encoder-handle`
   - Expected: metal_request.handle_kind equals `metal-encoder-pipeline`
   - Expected: metal_request.call_shape() equals `metal_compute_api`
   - Expected: metal_submit_failed.reason equals `backend-submit-failed`
   - Expected: metal_no_readback.reason equals `device-readback-required`
   - Expected: metal_zero_expected.reason equals `expected-checksum-required`
   - Expected: metal_mismatch.reason equals `device-readback-checksum-mismatch`
   - Expected: metal_executed.reason equals `readback-checksum-matched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 79 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires CUDA Vulkan and Metal artifact load submit and readback proof before device execution")
val cuda_module = generated_2d_module_artifact_evidence("cuda", GENERATED_2D_FILL, 64, 64, ".version 8.0 PTX", required_2d_entries(), 4096)
val cuda_load = generated_2d_artifact_load_evidence_from_module(cuda_module, true, 0, 9)
val cuda_missing_args = generated_2d_execution_request_from_load(cuda_load, 0)
val cuda_request = generated_2d_execution_request_from_load(cuda_load, 11)
val cuda_submit = generated_2d_submit_result(cuda_request, true, true)
val cuda_submit_failed = generated_2d_submit_result(cuda_request, true, false)
val cuda_no_readback = generated_2d_execution_evidence(cuda_submit, false, 2026070802, 2026070802)
val cuda_zero_expected = generated_2d_execution_evidence(cuda_submit, true, 0, 0)
val cuda_mismatch = generated_2d_execution_evidence(cuda_submit, true, 2026070802, 9)
val cuda_executed = generated_2d_execution_evidence(cuda_submit, true, 2026070802, 2026070802)

val module = generated_2d_module_artifact_evidence("vulkan", GENERATED_2D_FILL, 64, 64, "SPIR-V 1.3 Vulkan", required_2d_entries(), 4096)
val missing_queue = generated_2d_artifact_load_evidence_from_module(module, true, 0, 9)
val load = generated_2d_artifact_load_evidence_from_module(module, true, 7, 9)
val request = generated_2d_execution_request_from_load(load, 0)
val submit = generated_2d_submit_result(request, true, true)
val submit_failed = generated_2d_submit_result(request, true, false)
val no_readback = generated_2d_execution_evidence(submit, false, 2026070801, 2026070801)
val zero_expected = generated_2d_execution_evidence(submit, true, 0, 0)
val mismatch = generated_2d_execution_evidence(submit, true, 2026070801, 9)
val executed = generated_2d_execution_evidence(submit, true, 2026070801, 2026070801)

val metal_module = generated_2d_module_artifact_evidence("metal", GENERATED_2D_FILL, 64, 64, "MTLB metallib", required_2d_entries(), 4096)
val metal_missing_encoder = generated_2d_artifact_load_evidence_from_module(metal_module, true, 0, 9)
val metal_load = generated_2d_artifact_load_evidence_from_module(metal_module, true, 7, 9)
val metal_request = generated_2d_execution_request_from_load(metal_load, 0)
val metal_submit = generated_2d_submit_result(metal_request, true, true)
val metal_submit_failed = generated_2d_submit_result(metal_request, true, false)
val metal_no_readback = generated_2d_execution_evidence(metal_submit, false, 2026070803, 2026070803)
val metal_zero_expected = generated_2d_execution_evidence(metal_submit, true, 0, 0)
val metal_mismatch = generated_2d_execution_evidence(metal_submit, true, 2026070803, 9)
val metal_executed = generated_2d_execution_evidence(metal_submit, true, 2026070803, 2026070803)

expect(cuda_module.artifact_valid).to_be(true)
expect(cuda_load.loaded).to_be(true)
expect(cuda_missing_args.can_submit).to_be(false)
expect(cuda_missing_args.reason).to_equal("missing-args-pointer")
expect(cuda_request.handle_kind).to_equal("cuda-kernel-args")
expect(cuda_request.call_shape()).to_equal("cuda_launch_api")
expect(cuda_submit_failed.submitted).to_be(false)
expect(cuda_submit_failed.reason).to_equal("backend-submit-failed")
expect(cuda_no_readback.reason).to_equal("device-readback-required")
expect(cuda_zero_expected.reason).to_equal("expected-checksum-required")
expect(cuda_mismatch.reason).to_equal("device-readback-checksum-mismatch")
expect(cuda_executed.device_executed).to_be(true)
expect(cuda_executed.reason).to_equal("readback-checksum-matched")
expect(module.artifact_valid).to_be(true)
expect(missing_queue.loaded).to_be(false)
expect(missing_queue.reason).to_equal("missing-queue-or-encoder-handle")
expect(load.loaded).to_be(true)
expect(request.handle_kind).to_equal("vulkan-command-buffer-pipeline")
expect(request.call_shape()).to_equal("vulkan_compute_api")
expect(request.can_submit).to_be(true)
expect(submit.submitted).to_be(true)
expect(submit_failed.submitted).to_be(false)
expect(submit_failed.reason).to_equal("backend-submit-failed")
expect(no_readback.device_executed).to_be(false)
expect(no_readback.reason).to_equal("device-readback-required")
expect(zero_expected.device_executed).to_be(false)
expect(zero_expected.reason).to_equal("expected-checksum-required")
expect(mismatch.device_executed).to_be(false)
expect(mismatch.reason).to_equal("device-readback-checksum-mismatch")
expect(executed.device_executed).to_be(true)
expect(executed.reason).to_equal("readback-checksum-matched")
expect(metal_module.artifact_valid).to_be(true)
expect(metal_missing_encoder.loaded).to_be(false)
expect(metal_missing_encoder.reason).to_equal("missing-queue-or-encoder-handle")
expect(metal_load.loaded).to_be(true)
expect(metal_request.handle_kind).to_equal("metal-encoder-pipeline")
expect(metal_request.call_shape()).to_equal("metal_compute_api")
expect(metal_submit_failed.submitted).to_be(false)
expect(metal_submit_failed.reason).to_equal("backend-submit-failed")
expect(metal_no_readback.reason).to_equal("device-readback-required")
expect(metal_zero_expected.reason).to_equal("expected-checksum-required")
expect(metal_mismatch.reason).to_equal("device-readback-checksum-mismatch")
expect(metal_executed.device_executed).to_be(true)
expect(metal_executed.reason).to_equal("readback-checksum-matched")
```

</details>

#### keeps CPU SIMD as a CPU baseline instead of generated artifact offload

- keeps CPU SIMD as a CPU baseline instead of generated artifact offload
   - Expected: cpu.compute_target equals `cpu_simd`
   - Expected: cpu.execution_path equals `engine2d-cpu_simd`
   - Expected: cpu.typed_status equals `cpu-simd-baseline-ready`
   - Expected: vulkan_missing_runtime.compute_target equals `vulkan`
   - Expected: vulkan_missing_runtime.typed_status equals `vulkan-runtime-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps CPU SIMD as a CPU baseline instead of generated artifact offload")
val cpu = generated_2d_operation_provenance("cpu_simd", "fill", 64, 64, false, false, 0)
val vulkan_missing_runtime = generated_2d_operation_provenance("vulkan", "fill", 64, 64, false, true, 7)

expect(cpu.compute_target).to_equal("cpu_simd")
expect(cpu.execution_path).to_equal("engine2d-cpu_simd")
expect(cpu.generated_artifact_required).to_be(false)
expect(cpu.typed_status).to_equal("cpu-simd-baseline-ready")
expect(vulkan_missing_runtime.compute_target).to_equal("vulkan")
expect(vulkan_missing_runtime.generated_artifact_required).to_be(true)
expect(vulkan_missing_runtime.typed_status).to_equal("vulkan-runtime-unavailable")
```

</details>

#### marks text prep as CPU work while bitmap glyph raster is direct CUDA Vulkan and Metal offload

- marks text prep as CPU work while bitmap glyph raster is direct CUDA Vulkan and Metal offload
   - Expected: cuda_bitmap.generated_operation equals `bitmap_glyph_raster`
   - Expected: vulkan_bitmap.generated_operation equals `bitmap_glyph_raster`
   - Expected: metal_bitmap.generated_operation equals `bitmap_glyph_raster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks text prep as CPU work while bitmap glyph raster is direct CUDA Vulkan and Metal offload")
val cuda_text = generated_2d_operation_provenance("cuda", "text_blit", 64, 64, true, true, 7)
val vulkan_text = generated_2d_operation_provenance("vulkan", "text_blit", 64, 64, true, true, 7)
val metal_text = generated_2d_operation_provenance("metal", "text_blit", 64, 64, true, true, 7)
val cuda_bitmap = generated_2d_operation_provenance("cuda", "bitmap_glyph_raster", 64, 64, true, true, 7)
val vulkan_bitmap = generated_2d_operation_provenance("vulkan", "bitmap_glyph_raster", 64, 64, true, true, 7)
val metal_bitmap = generated_2d_operation_provenance("metal", "bitmap_glyph_raster", 64, 64, true, true, 7)

expect(cuda_text.cpu_preprocess_required).to_be(true)
expect(vulkan_text.cpu_preprocess_required).to_be(true)
expect(metal_text.cpu_preprocess_required).to_be(true)
expect(cuda_bitmap.cpu_preprocess_required).to_be(false)
expect(vulkan_bitmap.cpu_preprocess_required).to_be(false)
expect(metal_bitmap.cpu_preprocess_required).to_be(false)
expect(cuda_bitmap.generated_operation).to_equal("bitmap_glyph_raster")
expect(vulkan_bitmap.generated_operation).to_equal("bitmap_glyph_raster")
expect(metal_bitmap.generated_operation).to_equal("bitmap_glyph_raster")
expect(cuda_bitmap.ready).to_be(true)
expect(vulkan_bitmap.ready).to_be(true)
expect(metal_bitmap.ready).to_be(true)
```

</details>

#### routes fill copy alpha and scroll families to direct CUDA Vulkan and Metal generated kernels

- routes fill copy alpha and scroll families to direct CUDA Vulkan and Metal generated kernels


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes fill copy alpha and scroll families to direct CUDA Vulkan and Metal generated kernels")
expect_direct_gpu_op("cuda", "fill", "fill")
expect_direct_gpu_op("vulkan", "fill", "fill")
expect_direct_gpu_op("metal", "fill", "fill")
expect_direct_gpu_op("cuda", "image_blit", "copy")
expect_direct_gpu_op("vulkan", "image_blit", "copy")
expect_direct_gpu_op("metal", "image_blit", "copy")
expect_direct_gpu_op("cuda", "alpha_blend", "alpha_blend")
expect_direct_gpu_op("vulkan", "alpha_blend", "alpha_blend")
expect_direct_gpu_op("metal", "alpha_blend", "alpha_blend")
expect_direct_gpu_op("cuda", "scroll", "scroll")
expect_direct_gpu_op("vulkan", "scroll", "scroll")
expect_direct_gpu_op("metal", "scroll", "scroll")
```

</details>

#### reports backend specific not-ready reasons before generated GPU offload

- reports backend specific not-ready reasons before generated GPU offload


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports backend specific not-ready reasons before generated GPU offload")
expect_gpu_not_ready("cuda", false, true, 7, "cuda-runtime-unavailable")
expect_gpu_not_ready("cuda", true, false, 7, "cuda-module-unavailable")
expect_gpu_not_ready("cuda", true, true, 0, "args-unavailable")
expect_gpu_not_ready("vulkan", false, true, 7, "vulkan-runtime-unavailable")
expect_gpu_not_ready("vulkan", true, false, 7, "vulkan-pipeline-unavailable")
expect_gpu_not_ready("vulkan", true, true, 0, "args-unavailable")
expect_gpu_not_ready("metal", false, true, 7, "metal-runtime-unavailable")
expect_gpu_not_ready("metal", true, false, 7, "metal-pipeline-unavailable")
expect_gpu_not_ready("metal", true, true, 0, "args-unavailable")
```

</details>

#### rejects unsupported families and invalid dimensions before generated GPU offload

- rejects unsupported families and invalid dimensions before generated GPU offload


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unsupported families and invalid dimensions before generated GPU offload")
expect_gpu_plan_rejected("cuda", "bezier_path", 64, 64, "unsupported-operation-family")
expect_gpu_plan_rejected("vulkan", "bezier_path", 64, 64, "unsupported-operation-family")
expect_gpu_plan_rejected("metal", "bezier_path", 64, 64, "unsupported-operation-family")
expect_gpu_plan_rejected("cuda", "fill", 0, 64, "invalid-dimensions")
expect_gpu_plan_rejected("vulkan", "fill", 64, 0, "invalid-dimensions")
expect_gpu_plan_rejected("metal", "fill", -1, 64, "invalid-dimensions")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D generated kernel dispatch.
- Engine2D generated kernel dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `62ac40fdd0dc9abe95ef1e8f53c12a3617a491ca64b1e65843e64103f9626174`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62ac40fdd0dc9abe95ef1e8f53c12a3617a491ca64b1e65843e64103f9626174`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62ac40fdd0dc9abe95ef1e8f53c12a3617a491ca64b1e65843e64103f9626174`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces CUDA Vulkan and Metal generated 2D launch plans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps CPU SIMD as a CPU baseline instead of generated artifact offload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.spl:173:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks text prep as CPU work while bitmap glyph raster is direct CUDA Vulkan and Metal offload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
