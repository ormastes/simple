# Session Support Specification

> <details>

<!-- sdn-diagram:id=session_support_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=session_support_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

session_support_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=session_support_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Support Specification

## Scenarios

### GPU compute session shared support

#### normalizes readback status decisions for GPU backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unavailable = gpu_session_readback_status("cuda", false, 11, 11, "cuda-readback-required", "cuda-checksum-required", "cuda-checksum-matched", "cuda-checksum-mismatch")
val invalid = gpu_session_readback_status("rocm", true, 0, 11, "rocm-readback-required", "rocm-checksum-required", "rocm-checksum-matched", "rocm-checksum-mismatch")
val matched = gpu_session_readback_status("opencl", true, 22, 22, "opencl-readback-required", "opencl-checksum-required", "opencl-checksum-matched", "opencl-checksum-mismatch")
val mismatch = gpu_session_readback_status("opencl", true, 22, 23, "opencl-readback-required", "opencl-checksum-required", "opencl-checksum-matched", "opencl-checksum-mismatch")

expect(unavailable.success).to_equal(false)
expect(unavailable.status_code).to_equal("readback-unavailable")
expect(unavailable.reason).to_equal("cuda-readback-required")
expect(invalid.status_code).to_equal("invalid-checksum")
expect(invalid.reason).to_equal("rocm-checksum-required")
expect(matched.success).to_equal(true)
expect(matched.status_code).to_equal("readback-matched")
expect(matched.reason).to_equal("opencl-checksum-matched")
expect(mismatch.status_code).to_equal("readback-mismatch")
expect(mismatch.diagnostic_text()).to_contain("backend=opencl")
```

</details>

#### normalizes generated launch gate decisions for CUDA Vulkan Metal HIP and OpenCL sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_args_gate = generated_2d_session_launch_gate("cuda", GENERATED_2D_FILL, 8, 8, true, true, 0)
val missing_vulkan_runtime_gate = generated_2d_session_launch_gate("vulkan", GENERATED_2D_FILL, 8, 8, false, true, 4096)
val missing_metal_pipeline_gate = generated_2d_session_launch_gate("metal", GENERATED_2D_FILL, 8, 8, true, false, 4096)
val missing_ffi_gate = generated_2d_session_launch_gate("rocm", GENERATED_2D_FILL, 8, 8, false, false, 4096)
val missing_module_gate = generated_2d_session_launch_gate("opencl", GENERATED_2D_FILL, 8, 8, true, false, 4096)
val ready_gate = generated_2d_session_launch_gate("cuda", GENERATED_2D_FILL, 8, 8, true, true, 4096)

val missing_args = gpu_session_launch_gate_status("cuda", missing_args_gate, false, "missing-cuda-ffi", "runtime-not-ready", "cuda-runtime-not-ready", "missing-module", "missing-cuda-module")
val missing_vulkan_runtime = gpu_session_launch_gate_status("vulkan", missing_vulkan_runtime_gate, false, "missing-vulkan-ffi", "vulkan-runtime-unavailable", "vulkan-runtime-unavailable", "vulkan-pipeline-unavailable", "vulkan-pipeline-unavailable")
val missing_metal_pipeline = gpu_session_launch_gate_status("metal", missing_metal_pipeline_gate, false, "missing-metal-ffi", "metal-runtime-unavailable", "metal-runtime-unavailable", "metal-pipeline-unavailable", "metal-pipeline-unavailable")
val missing_ffi = gpu_session_launch_gate_status("rocm", missing_ffi_gate, true, "missing-rocm-ffi", "runtime-not-ready", "rocm-runtime-not-ready", "missing-module", "missing-rocm-module")
val missing_opencl_program = gpu_session_launch_gate_status("opencl", missing_module_gate, false, "missing-opencl-ffi", "missing-program-or-queue", "missing-opencl-program-or-queue", "missing-program-or-queue", "missing-opencl-program-or-queue")
val ready = gpu_session_launch_gate_status("cuda", ready_gate, false, "missing-cuda-ffi", "runtime-not-ready", "cuda-runtime-not-ready", "missing-module", "missing-cuda-module")

expect(missing_args.status_code).to_equal("missing-args-pointer")
expect(missing_args.reason).to_equal("missing-generated-2d-args-pointer")
expect(missing_vulkan_runtime.status_code).to_equal("vulkan-runtime-unavailable")
expect(missing_vulkan_runtime.reason).to_equal("vulkan-runtime-unavailable")
expect(missing_metal_pipeline.status_code).to_equal("metal-pipeline-unavailable")
expect(missing_metal_pipeline.reason).to_equal("metal-pipeline-unavailable")
expect(missing_ffi.status_code).to_equal("missing-ffi")
expect(missing_ffi.reason).to_equal("missing-rocm-ffi")
expect(missing_opencl_program.status_code).to_equal("missing-program-or-queue")
expect(missing_opencl_program.reason).to_equal("missing-opencl-program-or-queue")
expect(ready.ready).to_equal(true)
expect(ready.status_code).to_equal("ready")
expect(ready.diagnostic_text()).to_contain("backend=cuda")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/session_support_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU compute session shared support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
