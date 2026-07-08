# Generated Kernel Dispatch Specification

> <details>

<!-- sdn-diagram:id=generated_kernel_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generated_kernel_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generated_kernel_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generated_kernel_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generated Kernel Dispatch Specification

## Scenarios

### Engine2D generated kernel dispatch

#### produces CUDA Vulkan and Metal generated 2D launch plans

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda_module = generated_2d_module_artifact_evidence("cuda", GENERATED_2D_FILL, 64, 64, ".version 8.0 PTX", required_2d_entries(), 4096)
val cuda_load = generated_2d_artifact_load_evidence_from_module(cuda_module, true, 0, 9)
val cuda_missing_args = generated_2d_execution_request_from_load(cuda_load, 0)
val cuda_request = generated_2d_execution_request_from_load(cuda_load, 11)
val cuda_submit = generated_2d_submit_result(cuda_request, true, true)
val cuda_executed = generated_2d_execution_evidence(cuda_submit, true, 2026070802, 2026070802)

val module = generated_2d_module_artifact_evidence("vulkan", GENERATED_2D_FILL, 64, 64, "SPIR-V 1.3 Vulkan", required_2d_entries(), 4096)
val missing_queue = generated_2d_artifact_load_evidence_from_module(module, true, 0, 9)
val load = generated_2d_artifact_load_evidence_from_module(module, true, 7, 9)
val request = generated_2d_execution_request_from_load(load, 0)
val submit = generated_2d_submit_result(request, true, true)
val no_readback = generated_2d_execution_evidence(submit, false, 2026070801, 2026070801)
val executed = generated_2d_execution_evidence(submit, true, 2026070801, 2026070801)

val metal_module = generated_2d_module_artifact_evidence("metal", GENERATED_2D_FILL, 64, 64, "MTLB metallib", required_2d_entries(), 4096)
val metal_missing_encoder = generated_2d_artifact_load_evidence_from_module(metal_module, true, 0, 9)
val metal_load = generated_2d_artifact_load_evidence_from_module(metal_module, true, 7, 9)
val metal_request = generated_2d_execution_request_from_load(metal_load, 0)
val metal_submit = generated_2d_submit_result(metal_request, true, true)
val metal_executed = generated_2d_execution_evidence(metal_submit, true, 2026070803, 2026070803)

expect(cuda_module.artifact_valid).to_be(true)
expect(cuda_load.loaded).to_be(true)
expect(cuda_missing_args.can_submit).to_be(false)
expect(cuda_missing_args.reason).to_equal("missing-args-pointer")
expect(cuda_request.handle_kind).to_equal("cuda-kernel-args")
expect(cuda_request.call_shape()).to_equal("cuda_launch_api")
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
expect(no_readback.device_executed).to_be(false)
expect(no_readback.reason).to_equal("device-readback-required")
expect(executed.device_executed).to_be(true)
expect(executed.reason).to_equal("readback-checksum-matched")
expect(metal_module.artifact_valid).to_be(true)
expect(metal_missing_encoder.loaded).to_be(false)
expect(metal_missing_encoder.reason).to_equal("missing-queue-or-encoder-handle")
expect(metal_load.loaded).to_be(true)
expect(metal_request.handle_kind).to_equal("metal-encoder-pipeline")
expect(metal_request.call_shape()).to_equal("metal_compute_api")
expect(metal_executed.device_executed).to_be(true)
expect(metal_executed.reason).to_equal("readback-checksum-matched")
```

</details>

#### keeps CPU SIMD as a CPU baseline instead of generated artifact offload

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D generated kernel dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
