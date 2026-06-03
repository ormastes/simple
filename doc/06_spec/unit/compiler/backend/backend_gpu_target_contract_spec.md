# Backend Gpu Target Contract Specification

> <details>

<!-- sdn-diagram:id=backend_gpu_target_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_gpu_target_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_gpu_target_contract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_gpu_target_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Gpu Target Contract Specification

## Scenarios

### compiler GPU target contract

#### routes OpenCL codegen targets to the OpenCL backend

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(select_backend(CodegenTarget.OpenClC, nil)).to_equal(BackendKind.OpenCl)
expect(select_backend(CodegenTarget.OpenClSpirv, nil)).to_equal(BackendKind.OpenCl)
expect(select_backend(CodegenTarget.CudaPtx, nil)).to_equal(BackendKind.Cuda)
expect(select_backend(CodegenTarget.HipHsaco, nil)).to_equal(BackendKind.Hip)
expect(select_backend(CodegenTarget.VulkanSpirv, nil)).to_equal(BackendKind.Vulkan)
```

</details>

#### includes HIP and OpenCL in GPU backend ordering after CUDA

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backends = gpu_backends()

expect(backends.len()).to_equal(4)
expect(backends[0]).to_equal(BackendKind.Cuda)
expect(backends[1]).to_equal(BackendKind.Hip)
expect(backends[2]).to_equal(BackendKind.OpenCl)
expect(backends[3]).to_equal(BackendKind.Vulkan)
```

</details>

#### parses HIP backend names used by ROCm toolchains

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hip = backend_for_name("hip")
val hip_cpp = backend_for_name("hip-cpp")
val hsaco = backend_for_name("hsaco")
val rocm = backend_for_name("rocm")

expect(hip.?).to_equal(true)
expect(hip_cpp.?).to_equal(true)
expect(hsaco.?).to_equal(true)
expect(rocm.?).to_equal(true)
```

</details>

#### keeps CUDA backend target-aware for tagged GPU kernels

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CudaBackend.accepts_gpu_kernel_target(make_gpu_kernel("cuda_kernel", "cuda"))).to_equal(true)
expect(CudaBackend.accepts_gpu_kernel_target(make_gpu_kernel("auto_kernel", "auto"))).to_equal(true)
expect(CudaBackend.accepts_gpu_kernel_target(make_gpu_kernel("opencl_kernel", "opencl"))).to_equal(false)
```

</details>

#### uses backend order metadata to keep auto GPU kernels on the selected backend

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda_only = make_gpu_kernel_with_order("cuda_only", "auto", "cuda")
val opencl_only = make_gpu_kernel_with_order("opencl_only", "auto", "opencl")
val both = make_gpu_kernel_with_order("both", "auto", "opencl,cuda")

expect(CudaBackend.accepts_gpu_kernel_target(cuda_only)).to_equal(true)
expect(CudaBackend.accepts_gpu_kernel_target(opencl_only)).to_equal(false)
expect(CudaBackend.accepts_gpu_kernel_target(both)).to_equal(true)
expect(OpenClBackend.accepts_gpu_kernel(cuda_only)).to_equal(false)
expect(OpenClBackend.accepts_gpu_kernel(opencl_only)).to_equal(true)
expect(OpenClBackend.accepts_gpu_kernel(both)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/backend_gpu_target_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compiler GPU target contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
