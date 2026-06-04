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
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generated Kernel Dispatch Specification

## Scenarios

### Engine2D generated 2D kernel dispatch metadata

#### maps CUDA to PTX generated 2D kernels

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = generated_2d_dispatch_for_backend("cuda")

expect(dispatch.active).to_equal(true)
expect(dispatch.compute_target).to_equal("cuda")
expect(dispatch.source_format).to_equal("cuda-c")
expect(dispatch.binary_format).to_equal("ptx")
expect(dispatch.kernel_count).to_equal(4)
expect(dispatch.kernel_entry(GENERATED_2D_FILL)).to_equal("simple_2d_fill_u32")
expect(dispatch.artifact_suffix(GENERATED_2D_FILL)).to_equal("simple_2d_fill_u32.ptx")
expect(dispatch.module_artifact_name()).to_equal("simple_2d_optimization.ptx")
```

</details>

#### maps ROCm through the HIP/HSACO generated kernel path

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = generated_2d_dispatch_for_backend("rocm")

expect(dispatch.active).to_equal(true)
expect(dispatch.backend_name).to_equal("rocm")
expect(dispatch.compute_target).to_equal("hip")
expect(dispatch.source_format).to_equal("hip-cpp")
expect(dispatch.binary_format).to_equal("hsaco")
expect(dispatch.kernel_entry(GENERATED_2D_ALPHA)).to_equal("simple_2d_alpha_u32")
expect(dispatch.artifact_suffix(GENERATED_2D_ALPHA)).to_equal("simple_2d_alpha_u32.hsaco")
expect(dispatch.required_entries()).to_contain("simple_2d_scroll_u32")
```

</details>

#### maps OpenCL and Metal to their binary artifact formats

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opencl = generated_2d_dispatch_for_backend("opencl")
val metal = generated_2d_dispatch_for_backend("metal")

expect(opencl.source_format).to_equal("opencl-c")
expect(opencl.binary_format).to_equal("spirv")
expect(opencl.kernel_entry(GENERATED_2D_COPY)).to_equal("simple_2d_copy_u32")
expect(metal.source_format).to_equal("metal-shading-language")
expect(metal.binary_format).to_equal("metallib")
expect(metal.kernel_entry(GENERATED_2D_SCROLL)).to_equal("simple_2d_scroll_u32")
```

</details>

#### rejects unsupported dispatch backends without fallback

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = generated_2d_dispatch_for_backend("cpu")

expect(dispatch.active).to_equal(false)
expect(dispatch.compute_target).to_equal("unsupported")
expect(dispatch.supports_kernel(GENERATED_2D_FILL)).to_equal(false)
expect(dispatch.artifact_suffix(GENERATED_2D_FILL)).to_equal("")
expect(dispatch.module_artifact_name()).to_equal("")
```

</details>

#### exposes generated dispatch as Engine2D optimization provider metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch = generated_2d_dispatch_for_backend("metal")
val provider = generated_2d_dispatch_provider(dispatch)

expect(provider.provider_kind).to_equal("generated_2d_kernel_dispatch")
expect(provider.target_arch).to_equal("metal")
expect(provider.target_features).to_equal("metallib")
expect(provider.hit_count).to_equal(4)
expect(provider.change_count).to_equal(1)
expect(provider.active).to_equal(true)
```

</details>

#### builds CUDA runtime launch plans for generated 2D kernels

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = generated_2d_launch_plan("cuda", GENERATED_2D_FILL, 640, 480)

expect(plan.dispatch_ready).to_equal(true)
expect(plan.entry_name).to_equal("simple_2d_fill_u32")
expect(plan.artifact_name).to_equal("simple_2d_optimization.ptx")
expect(plan.required_entries).to_contain("simple_2d_copy_u32")
expect(plan.launch_api).to_equal("rt_cuda_launch_kernel")
expect(plan.grid_x).to_equal(1200)
expect(plan.block_x).to_equal(256)
expect(plan.args_layout).to_equal("dst,width,height,color_u32")
```

</details>

#### uses backend-specific launch APIs for HIP, OpenCL, and Metal

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hip = generated_2d_launch_plan("rocm", GENERATED_2D_ALPHA, 16, 16)
val opencl = generated_2d_launch_plan("opencl", GENERATED_2D_COPY, 32, 4)
val metal = generated_2d_launch_plan("metal", GENERATED_2D_SCROLL, 10, 10)

expect(hip.launch_api).to_equal("rt_rocm_launch_kernel")
expect(hip.artifact_name).to_equal("simple_2d_optimization.hsaco")
expect(opencl.launch_api).to_equal("clEnqueueNDRangeKernel")
expect(opencl.artifact_name).to_equal("simple_2d_optimization.spirv")
expect(metal.launch_api).to_equal("MTLComputeCommandEncoder.dispatchThreads")
expect(metal.artifact_name).to_equal("simple_2d_optimization.metallib")
expect(metal.args_layout).to_equal("src,dst,width,height,delta_y")
```

</details>

#### fails generated launch plans closed for unsupported backends and dimensions

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsupported = generated_2d_launch_plan("cpu", GENERATED_2D_FILL, 64, 64)
val invalid = generated_2d_launch_plan("cuda", GENERATED_2D_COPY, 0, 64)
val rect = generated_2d_launch_plan("opencl", "rect_filled", 64, 64)

expect(unsupported.dispatch_ready).to_equal(false)
expect(unsupported.reason).to_equal("backend-inactive")
expect(unsupported.launch_api).to_equal("none")
expect(invalid.dispatch_ready).to_equal(false)
expect(invalid.reason).to_equal("invalid-dimensions")
expect(rect.dispatch_ready).to_equal(false)
expect(rect.reason).to_equal("unsupported-operation")
expect(rect.launch_api).to_equal("none")
```

</details>

#### binds CUDA and ROCm launch plans to prepared runtime execution calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = generated_2d_execution_request("cuda", GENERATED_2D_FILL, 64, 64, 0, 77, 2048)
val rocm = generated_2d_execution_request("rocm", GENERATED_2D_ALPHA, 32, 32, 0, 88, 4096)

expect(cuda.can_submit).to_equal(true)
expect(cuda.handle_kind).to_equal("cuda-kernel-args")
expect(cuda.call_shape()).to_equal("rt_cuda_launch_kernel(kernel,gx,gy,gz,bx,by,bz,shared_mem,args_ptr)")
expect(rocm.can_submit).to_equal(true)
expect(rocm.handle_kind).to_equal("rocm-kernel-args")
expect(rocm.call_shape()).to_equal("rt_rocm_launch_kernel(kernel,gx,gy,gz,bx,by,bz,shared_mem,args_ptr)")
```

</details>

#### binds OpenCL and Metal launch plans to queue or encoder execution calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opencl = generated_2d_execution_request("opencl", GENERATED_2D_COPY, 16, 16, 11, 22, 0)
val metal = generated_2d_execution_request("metal", GENERATED_2D_SCROLL, 16, 16, 33, 44, 0)

expect(opencl.can_submit).to_equal(true)
expect(opencl.handle_kind).to_equal("opencl-queue-kernel")
expect(opencl.call_shape()).to_equal("clEnqueueNDRangeKernel(queue,kernel,global_range,local_range)")
expect(metal.can_submit).to_equal(true)
expect(metal.handle_kind).to_equal("metal-encoder-pipeline")
expect(metal.call_shape()).to_equal("metal_sffi_dispatch_compute(encoder,pipeline,gx,gy,gz,bx,by,bz)")
```

</details>

#### builds OpenCL launch evidence shapes for every generated 2D operation

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fill = generated_2d_execution_request("opencl", GENERATED_2D_FILL, 16, 16, 11, 21, 0)
val copy = generated_2d_execution_request("opencl", GENERATED_2D_COPY, 16, 16, 11, 22, 0)
val alpha = generated_2d_execution_request("opencl", GENERATED_2D_ALPHA, 16, 16, 11, 23, 0)
val scroll = generated_2d_execution_request("opencl", GENERATED_2D_SCROLL, 16, 16, 11, 24, 0)

expect(fill.can_submit).to_equal(true)
expect(fill.plan.entry_name).to_equal("simple_2d_fill_u32")
expect(fill.plan.launch_api).to_equal("clEnqueueNDRangeKernel")
expect(copy.plan.entry_name).to_equal("simple_2d_copy_u32")
expect(alpha.plan.entry_name).to_equal("simple_2d_alpha_u32")
expect(scroll.plan.entry_name).to_equal("simple_2d_scroll_u32")
expect(scroll.call_shape()).to_equal("clEnqueueNDRangeKernel(queue,kernel,global_range,local_range)")
```

</details>

#### rejects generated execution requests with missing runtime handles

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_args = generated_2d_execution_request("cuda", GENERATED_2D_FILL, 16, 16, 0, 77, 0)
val missing_queue = generated_2d_execution_request("metal", GENERATED_2D_SCROLL, 16, 16, 0, 44, 0)
val bad_plan = generated_2d_execution_request("cpu", GENERATED_2D_FILL, 16, 16, 0, 44, 2048)

expect(missing_args.can_submit).to_equal(false)
expect(missing_args.reason).to_equal("missing-args-pointer")
expect(missing_queue.can_submit).to_equal(false)
expect(missing_queue.reason).to_equal("missing-queue-or-encoder-handle")
expect(bad_plan.can_submit).to_equal(false)
expect(bad_plan.reason).to_equal("backend-inactive")
```

</details>

#### requires generated artifacts to load before building runtime execution requests

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda_load = generated_2d_artifact_load_evidence("cuda", GENERATED_2D_FILL, 16, 16, true, true, 0, 77)
val metal_load = generated_2d_artifact_load_evidence("metal", GENERATED_2D_SCROLL, 16, 16, true, true, 33, 44)
val cuda_request = generated_2d_execution_request_from_load(cuda_load, 2048)
val metal_request = generated_2d_execution_request_from_load(metal_load, 0)

expect(cuda_load.loaded).to_equal(true)
expect(cuda_load.reason).to_equal("loaded")
expect(cuda_request.can_submit).to_equal(true)
expect(cuda_request.call_shape()).to_contain("rt_cuda_launch_kernel")
expect(metal_load.loaded).to_equal(true)
expect(metal_request.can_submit).to_equal(true)
expect(metal_request.call_shape()).to_contain("metal_sffi_dispatch_compute")
```

</details>

#### validates shared generated 2D module artifacts before loading

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val valid = generated_2d_module_artifact_evidence("cuda", GENERATED_2D_FILL, 16, 16, ".version 8.0", ".entry simple_2d_fill_u32 .entry simple_2d_copy_u32 .entry simple_2d_alpha_u32 .entry simple_2d_scroll_u32", 4486)
val missing = generated_2d_module_artifact_evidence("cuda", GENERATED_2D_FILL, 16, 16, ".version 8.0", ".entry simple_2d_fill_u32 .entry simple_2d_copy_u32 .entry simple_2d_alpha_u32", 4486)
val load = generated_2d_artifact_load_evidence_from_module(valid, true, 0, 77)
val blocked = generated_2d_artifact_load_evidence_from_module(missing, true, 0, 77)

expect(valid.artifact_valid).to_equal(true)
expect(valid.reason).to_equal("pass")
expect(valid.summary()).to_contain("simple_2d_optimization.ptx")
expect(load.loaded).to_equal(true)
expect(missing.artifact_valid).to_equal(false)
expect(missing.reason).to_equal("missing-entry-symbol:simple_2d_scroll_u32")
expect(blocked.loaded).to_equal(false)
expect(blocked.reason).to_equal("artifact-not-verified")
```

</details>

#### keeps OpenCL generated modules fail-closed without runtime and readback evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = generated_2d_module_artifact_evidence("opencl", GENERATED_2D_COPY, 16, 16, "SPIR-V 1.5", "OpEntryPoint GLCompute %simple_2d_fill_u32 \"simple_2d_fill_u32\" OpEntryPoint GLCompute %simple_2d_copy_u32 \"simple_2d_copy_u32\" OpEntryPoint GLCompute %simple_2d_alpha_u32 \"simple_2d_alpha_u32\" OpEntryPoint GLCompute %simple_2d_scroll_u32 \"simple_2d_scroll_u32\"", 4096)
val no_runtime = generated_2d_artifact_load_evidence_from_module(module, false, 11, 22)
val request = generated_2d_execution_request_from_load(no_runtime, 0)
val submit = generated_2d_submit_result(request, false, true)
val evidence = generated_2d_execution_evidence(submit, false, 1234, 1234)

expect(module.artifact_valid).to_equal(true)
expect(module.plan.artifact_name).to_equal("simple_2d_optimization.spirv")
expect(no_runtime.loaded).to_equal(false)
expect(no_runtime.reason).to_equal("runtime-unavailable")
expect(request.can_submit).to_equal(false)
expect(submit.submitted).to_equal(false)
expect(evidence.device_executed).to_equal(false)
expect(evidence.status_code).to_equal("not-submitted")
```

</details>

#### fails generated artifact loads closed for bad artifacts runtime or handles

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_artifact = generated_2d_artifact_load_evidence("cuda", GENERATED_2D_FILL, 16, 16, false, true, 0, 77)
val no_runtime = generated_2d_artifact_load_evidence("cuda", GENERATED_2D_FILL, 16, 16, true, false, 0, 77)
val missing_kernel = generated_2d_artifact_load_evidence("cuda", GENERATED_2D_FILL, 16, 16, true, true, 0, 0)
val missing_queue = generated_2d_artifact_load_evidence("opencl", GENERATED_2D_COPY, 16, 16, true, true, 0, 22)
val request = generated_2d_execution_request_from_load(bad_artifact, 2048)

expect(bad_artifact.loaded).to_equal(false)
expect(bad_artifact.reason).to_equal("artifact-not-verified")
expect(no_runtime.loaded).to_equal(false)
expect(no_runtime.reason).to_equal("runtime-unavailable")
expect(missing_kernel.loaded).to_equal(false)
expect(missing_kernel.reason).to_equal("missing-kernel-or-pipeline-handle")
expect(missing_queue.loaded).to_equal(false)
expect(missing_queue.reason).to_equal("missing-queue-or-encoder-handle")
expect(request.can_submit).to_equal(false)
expect(request.reason).to_equal("artifact-not-verified")
```

</details>

#### records generated kernel submit status without pretending runtime availability

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = generated_2d_execution_request("cuda", GENERATED_2D_FILL, 16, 16, 0, 77, 2048)
val missing = generated_2d_execution_request("cuda", GENERATED_2D_FILL, 16, 16, 0, 77, 0)
val unavailable = generated_2d_submit_result(ready, false, true)
val failed = generated_2d_submit_result(ready, true, false)
val submitted = generated_2d_submit_result(ready, true, true)
val not_ready = generated_2d_submit_result(missing, true, true)

expect(unavailable.attempted).to_equal(false)
expect(unavailable.submitted).to_equal(false)
expect(unavailable.status_code).to_equal("runtime-unavailable")
expect(failed.attempted).to_equal(true)
expect(failed.submitted).to_equal(false)
expect(failed.status_code).to_equal("submit-failed")
expect(submitted.attempted).to_equal(true)
expect(submitted.submitted).to_equal(true)
expect(submitted.status_code).to_equal("submitted")
expect(not_ready.attempted).to_equal(false)
expect(not_ready.status_code).to_equal("not-ready")
expect(not_ready.reason).to_equal("missing-args-pointer")
```

</details>

#### requires readback checksum evidence before claiming device execution

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = generated_2d_execution_request("cuda", GENERATED_2D_FILL, 16, 16, 0, 77, 2048)
val submitted = generated_2d_submit_result(ready, true, true)
val no_readback = generated_2d_execution_evidence(submitted, false, 1234, 1234)
val mismatch = generated_2d_execution_evidence(submitted, true, 1234, 999)
val verified = generated_2d_execution_evidence(submitted, true, 1234, 1234)

expect(no_readback.device_executed).to_equal(false)
expect(no_readback.status_code).to_equal("readback-unavailable")
expect(mismatch.device_executed).to_equal(false)
expect(mismatch.status_code).to_equal("readback-mismatch")
expect(verified.device_executed).to_equal(true)
expect(verified.status_code).to_equal("device-executed")
expect(verified.summary()).to_contain("executed=true")
```

</details>

#### does not claim execution when submit failed or expected checksum is invalid

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = generated_2d_execution_request("metal", GENERATED_2D_SCROLL, 16, 16, 33, 44, 0)
val failed = generated_2d_submit_result(ready, true, false)
val submitted = generated_2d_submit_result(ready, true, true)
val failed_evidence = generated_2d_execution_evidence(failed, true, 1234, 1234)
val invalid_checksum = generated_2d_execution_evidence(submitted, true, 0, 0)

expect(failed_evidence.device_executed).to_equal(false)
expect(failed_evidence.status_code).to_equal("not-submitted")
expect(invalid_checksum.device_executed).to_equal(false)
expect(invalid_checksum.status_code).to_equal("invalid-expected-checksum")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/generated_kernel_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D generated 2D kernel dispatch metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
