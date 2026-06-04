# Gpu Generated 2d Contract Specification

> <details>

<!-- sdn-diagram:id=gpu_generated_2d_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_generated_2d_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_generated_2d_contract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_generated_2d_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Generated 2d Contract Specification

## Scenarios

### Shared generated Engine2D GPU backend compile contract

#### normalizes CUDA HIP OpenCL and Metal generated artifacts into one contract shape

<details>
<summary>Executable SPipe</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32 simple_2d_scroll_u32"
val spirv_exported = "OpEntryPoint GLCompute %simple_2d_fill_u32 \"simple_2d_fill_u32\" OpEntryPoint GLCompute %simple_2d_copy_u32 \"simple_2d_copy_u32\" OpEntryPoint GLCompute %simple_2d_alpha_u32 \"simple_2d_alpha_u32\" OpEntryPoint GLCompute %simple_2d_scroll_u32 \"simple_2d_scroll_u32\""
val cuda = cuda_generated_2d_compile_contract("simple_2d_optimization", ".version 8.0", plain_exported, 4096)
val hip = hip_generated_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", plain_exported, 4096)
val opencl = opencl_generated_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.5", spirv_exported, 4096)
val metal = metal_generated_2d_compile_contract("simple_2d_optimization", "MTLB metallib", plain_exported, 4096)

expect(cuda.backend_name).to_equal("cuda")
expect(cuda.ready).to_equal(true)
expect(cuda.plan.source_format).to_equal("cuda-c")
expect(cuda.plan.binary_format).to_equal("ptx")
expect(cuda.source).to_contain("extern \"C\" __global__ void simple_2d_fill_u32")
expect(hip.backend_name).to_equal("hip")
expect(hip.ready).to_equal(true)
expect(hip.plan.source_format).to_equal("hip-cpp")
expect(hip.plan.binary_format).to_equal("hsaco")
expect(hip.source).to_contain("blockIdx.x * blockDim.x + threadIdx.x")
expect(opencl.backend_name).to_equal("opencl")
expect(opencl.ready).to_equal(true)
expect(opencl.plan.source_format).to_equal("opencl-c")
expect(opencl.plan.binary_format).to_equal("spirv")
expect(opencl.source).to_contain("__kernel void simple_2d_fill_u32")
expect(opencl.summary()).to_contain("backend=opencl")
expect(metal.backend_name).to_equal("metal")
expect(metal.ready).to_equal(true)
expect(metal.plan.source_format).to_equal("metal-shading-language")
expect(metal.plan.binary_format).to_equal("metallib")
expect(metal.source).to_contain("kernel void simple_2d_fill_u32")
expect(metal.summary()).to_contain("backend=metal")
```

</details>

#### keeps backend-specific artifact magic diagnostics in the shared contract

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_exported = "simple_2d_fill_u32 simple_2d_copy_u32 simple_2d_alpha_u32 simple_2d_scroll_u32"
val spirv_exported = "OpEntryPoint GLCompute %simple_2d_fill_u32 \"simple_2d_fill_u32\" OpEntryPoint GLCompute %simple_2d_copy_u32 \"simple_2d_copy_u32\" OpEntryPoint GLCompute %simple_2d_alpha_u32 \"simple_2d_alpha_u32\" OpEntryPoint GLCompute %simple_2d_scroll_u32 \"simple_2d_scroll_u32\""
val bad_cuda = cuda_generated_2d_compile_contract("simple_2d_optimization", "ELF AMDGCN HSACO", plain_exported, 4096)
val bad_hip = hip_generated_2d_compile_contract("simple_2d_optimization", ".version 8.0", plain_exported, 4096)
val bad_opencl = opencl_generated_2d_compile_contract("simple_2d_optimization", ".version 8.0", spirv_exported, 4096)
val bad_metal = metal_generated_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.5", plain_exported, 4096)

expect(bad_cuda.ready).to_equal(false)
expect(bad_cuda.status).to_equal("artifact-magic-mismatch")
expect(bad_cuda.diagnostic).to_contain("CUDA artifact rejected")
expect(bad_hip.ready).to_equal(false)
expect(bad_hip.status).to_equal("artifact-magic-mismatch")
expect(bad_hip.diagnostic).to_contain("HIP artifact rejected")
expect(bad_opencl.ready).to_equal(false)
expect(bad_opencl.status).to_equal("artifact-magic-mismatch")
expect(bad_opencl.diagnostic).to_contain("OpenCL artifact rejected")
expect(bad_metal.ready).to_equal(false)
expect(bad_metal.status).to_equal("artifact-magic-mismatch")
expect(bad_metal.diagnostic).to_contain("Metal artifact rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Shared generated Engine2D GPU backend compile contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
