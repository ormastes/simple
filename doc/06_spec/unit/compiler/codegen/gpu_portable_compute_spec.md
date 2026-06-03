# Gpu Portable Compute Specification

> <details>

<!-- sdn-diagram:id=gpu_portable_compute_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_portable_compute_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_portable_compute_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_portable_compute_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Portable Compute Specification

## Scenarios

### portable GPU compute emitter

#### emits CUDA fill source with PTX artifact label

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = emit_portable_u32_fill_kernel(PortableComputeTarget.Cuda, "fill_u32")
expect(artifact.target_name()).to_equal("cuda")
expect(artifact.binary_format).to_equal("ptx")
expect(artifact.source).to_contain("extern \"C\" __global__ void fill_u32")
expect(artifact.source).to_contain("blockIdx.x * blockDim.x + threadIdx.x")
expect(artifact.source).to_contain("dst[i] = value;")
```

</details>

#### emits HIP fill source with HSACO artifact label

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = emit_portable_u32_fill_kernel(PortableComputeTarget.Hip, "fill_u32")
expect(artifact.target_name()).to_equal("hip")
expect(artifact.binary_format).to_equal("hsaco")
expect(artifact.source).to_contain("__global__ void fill_u32")
expect(artifact.source).to_contain("blockIdx.x * blockDim.x + threadIdx.x")
```

</details>

#### emits OpenCL C fill source with SPIR-V artifact label

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = emit_portable_u32_fill_kernel(PortableComputeTarget.OpenCl, "fill_u32")
expect(artifact.target_name()).to_equal("opencl")
expect(artifact.binary_format).to_equal("spirv")
expect(artifact.source).to_contain("__kernel void fill_u32")
expect(artifact.source).to_contain("__global uint* dst")
expect(artifact.source).to_contain("get_global_id(0)")
```

</details>

#### emits Metal fill source with metallib artifact label

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = emit_portable_u32_fill_kernel(PortableComputeTarget.Metal, "fill_u32")
expect(artifact.target_name()).to_equal("metal")
expect(artifact.binary_format).to_equal("metallib")
expect(artifact.source).to_contain("kernel void fill_u32")
expect(artifact.source).to_contain("device uint* dst [[buffer(0)]]")
expect(artifact.source).to_contain("uint gid [[thread_position_in_grid]]")
```

</details>

#### emits one add kernel shape across all compute targets

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = emit_portable_u32_add_kernel(PortableComputeTarget.Cuda, "add_u32")
val hip = emit_portable_u32_add_kernel(PortableComputeTarget.Hip, "add_u32")
val opencl = emit_portable_u32_add_kernel(PortableComputeTarget.OpenCl, "add_u32")
val metal = emit_portable_u32_add_kernel(PortableComputeTarget.Metal, "add_u32")
expect(cuda.source).to_contain("out[i] = a[i] + b[i];")
expect(hip.source).to_contain("out[i] = a[i] + b[i];")
expect(opencl.source).to_contain("out[i] = a[i] + b[i];")
expect(metal.source).to_contain("out[i] = a[i] + b[i];")
```

</details>

#### builds target compile plans for source to binary artifacts

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = emit_portable_u32_fill_kernel(PortableComputeTarget.Cuda, "fill_u32")
val opencl = emit_portable_u32_fill_kernel(PortableComputeTarget.OpenCl, "fill_u32")
val metal = emit_portable_u32_fill_kernel(PortableComputeTarget.Metal, "fill_u32")

val cuda_plan = portable_compute_compile_plan(cuda, "fill_u32")
val opencl_plan = portable_compute_compile_plan(opencl, "fill_u32")
val metal_plan = portable_compute_compile_plan(metal, "fill_u32")

expect(cuda_plan.source_format).to_equal("cuda-c")
expect(cuda_plan.tool_hint).to_equal("nvrtc-or-nvcc")
expect(cuda_plan.artifact_path_suffix).to_equal("fill_u32.ptx")
expect(cuda_plan.produces_binary()).to_equal(true)
expect(opencl_plan.binary_format).to_equal("spirv")
expect(opencl_plan.tool_hint).to_equal("opencl-c-to-spirv")
expect(metal_plan.binary_format).to_equal("metallib")
expect(metal_plan.source_format).to_equal("metal-shading-language")
```

</details>

#### validates generated binary artifacts by target magic and exported entry

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Cuda, "fill_u32"), "fill_u32")
val hip_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Hip, "fill_u32"), "fill_u32")
val opencl_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.OpenCl, "fill_u32"), "fill_u32")
val metal_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Metal, "fill_u32"), "fill_u32")

val cuda = portable_compute_compiled_artifact_evidence(cuda_plan, ".version 8.0", ".entry fill_u32", 256)
val hip = portable_compute_compiled_artifact_evidence(hip_plan, "ELF AMDGCN HSACO", "fill_u32", 512)
val opencl = portable_compute_compiled_artifact_evidence(opencl_plan, "SPIR-V 1.5", "OpEntryPoint GLCompute %fill_u32 \"fill_u32\"", 384)
val metal = portable_compute_compiled_artifact_evidence(metal_plan, "MTLB metallib", "fill_u32", 448)

expect(cuda.artifact_valid).to_equal(true)
expect(hip.artifact_valid).to_equal(true)
expect(opencl.artifact_valid).to_equal(true)
expect(metal.artifact_valid).to_equal(true)
expect(metal.summary()).to_contain("valid=true")
```

</details>

#### fails generated binary evidence closed for missing bytes magic or symbol

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.OpenCl, "fill_u32"), "fill_u32")
val missing_bytes = portable_compute_compiled_artifact_evidence(plan, "SPIR-V 1.5", "fill_u32", 0)
val bad_magic = portable_compute_compiled_artifact_evidence(plan, "ELF", "fill_u32", 128)
val missing_symbol = portable_compute_compiled_artifact_evidence(plan, "SPIR-V 1.5", "other_kernel", 128)

expect(missing_bytes.artifact_valid).to_equal(false)
expect(missing_bytes.reason).to_equal("missing-artifact-bytes")
expect(bad_magic.artifact_valid).to_equal(false)
expect(bad_magic.reason).to_equal("artifact-magic-mismatch")
expect(missing_symbol.artifact_valid).to_equal(false)
expect(missing_symbol.reason).to_equal("missing-entry-symbol")
```

</details>

#### builds deterministic toolchain invocations for target binary generation

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Cuda, "fill_u32"), "fill_u32")
val hip_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Hip, "fill_u32"), "fill_u32")
val opencl_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.OpenCl, "fill_u32"), "fill_u32")
val metal_plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Metal, "fill_u32"), "fill_u32")

val cuda = portable_compute_toolchain_invocation(cuda_plan, "build/gpu/fill_u32.cu", "build/gpu/fill_u32.ptx", "nvcc", "")
val hip = portable_compute_toolchain_invocation(hip_plan, "build/gpu/fill_u32.hip.cpp", "build/gpu/fill_u32.hsaco", "hipcc", "")
val opencl = portable_compute_toolchain_invocation(opencl_plan, "build/gpu/fill_u32.cl", "build/gpu/fill_u32.spirv", "opencl-c-to-spirv", "")
val metal = portable_compute_toolchain_invocation(metal_plan, "build/gpu/fill_u32.metal", "build/gpu/fill_u32.metallib", "xcrun metal", "xcrun metallib")

expect(cuda.ready).to_equal(true)
expect(cuda.command_line).to_contain("nvcc --ptx")
expect(cuda.command_line).to_contain("--entry fill_u32")
expect(hip.command_line).to_contain("hipcc --genco")
expect(opencl.command_line).to_contain("-emit-spirv")
expect(metal.command_line).to_contain("xcrun metallib")
expect(metal.summary()).to_contain("ready=true")
```

</details>

#### fails toolchain invocations closed when required tools or paths are missing

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Metal, "fill_u32"), "fill_u32")
val missing_primary = portable_compute_toolchain_invocation(plan, "build/gpu/fill_u32.metal", "build/gpu/fill_u32.metallib", "", "xcrun metallib")
val missing_metallib = portable_compute_toolchain_invocation(plan, "build/gpu/fill_u32.metal", "build/gpu/fill_u32.metallib", "xcrun metal", "")
val missing_output = portable_compute_toolchain_invocation(plan, "build/gpu/fill_u32.metal", "", "xcrun metal", "xcrun metallib")

expect(missing_primary.ready).to_equal(false)
expect(missing_primary.reason).to_equal("missing-primary-tool")
expect(missing_metallib.ready).to_equal(false)
expect(missing_metallib.reason).to_equal("missing-metallib-tool")
expect(missing_output.ready).to_equal(false)
expect(missing_output.reason).to_equal("missing-output-path")
```

</details>

#### records toolchain compile results without accepting failed or invalid artifacts

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = portable_compute_compile_plan(emit_portable_u32_fill_kernel(PortableComputeTarget.Cuda, "fill_u32"), "fill_u32")
val request = portable_compute_toolchain_invocation(plan, "build/gpu/fill_u32.cu", "build/gpu/fill_u32.ptx", "nvcc", "")
val valid = portable_compute_compiled_artifact_evidence(plan, ".version 8.0", ".entry fill_u32", 256)
val invalid = portable_compute_compiled_artifact_evidence(plan, "ELF", ".entry fill_u32", 256)
val ok = portable_compute_compile_result(request, 0, valid)
val failed_tool = portable_compute_compile_result(request, 1, valid)
val failed_artifact = portable_compute_compile_result(request, 0, invalid)

expect(ok.ready).to_equal(true)
expect(ok.status).to_equal("compiled_artifact_verified")
expect(ok.diagnostic).to_equal("")
expect(failed_tool.ready).to_equal(false)
expect(failed_tool.status).to_equal("toolchain_failed")
expect(failed_tool.diagnostic).to_contain("toolchain exited with code 1")
expect(failed_artifact.ready).to_equal(false)
expect(failed_artifact.status).to_equal("artifact-magic-mismatch")
```

</details>

#### emits portable 2D optimization kernels for copy alpha and scroll

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val copy = emit_portable_2d_copy_u32_kernel(PortableComputeTarget.OpenCl)
val alpha = emit_portable_2d_alpha_u32_kernel(PortableComputeTarget.Cuda)
val scroll = emit_portable_2d_scroll_u32_kernel(PortableComputeTarget.Metal)

expect(copy.entry_name).to_equal("simple_2d_copy_u32")
expect(copy.source).to_contain("dst[i] = src[i];")
expect(alpha.entry_name).to_equal("simple_2d_alpha_u32")
expect(alpha.source).to_contain("unsigned int inv = 255u - alpha;")
expect(alpha.source).to_contain("0xff000000u")
expect(scroll.entry_name).to_equal("simple_2d_scroll_u32")
expect(scroll.source).to_contain("int sy = int(y) - delta_y;")
expect(scroll.source).to_contain("dst[i] = 0u;")
```

</details>

#### groups Simple-authored 2D optimization kernels per compute target

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = emit_portable_2d_optimization_kernels(PortableComputeTarget.Cuda)
val hip = emit_portable_2d_optimization_kernels(PortableComputeTarget.Hip)
val opencl = emit_portable_2d_optimization_kernels(PortableComputeTarget.OpenCl)
val metal = emit_portable_2d_optimization_kernels(PortableComputeTarget.Metal)

expect(cuda.len()).to_equal(4)
expect(hip[2].entry_name).to_equal("simple_2d_alpha_u32")
expect(opencl[3].binary_format).to_equal("spirv")
expect(metal[1].source).to_contain("[[buffer(1)]]")
```

</details>

#### builds one generated 2D optimization module per target with all required entries

<details>
<summary>Executable SPipe</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = emit_portable_2d_optimization_module(PortableComputeTarget.Cuda)
val opencl = emit_portable_2d_optimization_module(PortableComputeTarget.OpenCl)
val cuda_plan = portable_compute_2d_optimization_compile_plan(PortableComputeTarget.Cuda, "simple_2d_optimization")
val hip_plan = portable_compute_2d_optimization_compile_plan(PortableComputeTarget.Hip, "simple_2d_optimization")
val opencl_plan = portable_compute_2d_optimization_compile_plan(PortableComputeTarget.OpenCl, "simple_2d_optimization")
val metal_plan = portable_compute_2d_optimization_compile_plan(PortableComputeTarget.Metal, "simple_2d_optimization")

expect(cuda.entry_name).to_equal("simple_2d_fill_u32")
expect(cuda.source).to_contain("simple_2d_fill_u32")
expect(cuda.source).to_contain("simple_2d_copy_u32")
expect(cuda.source).to_contain("simple_2d_alpha_u32")
expect(cuda.source).to_contain("simple_2d_scroll_u32")
expect(opencl.source).to_contain("__kernel void simple_2d_copy_u32")
expect(metal_plan.required_symbols).to_contain("simple_2d_scroll_u32")
expect(metal_plan.artifact_path_suffix).to_equal("simple_2d_optimization.metallib")
expect(cuda_plan.required_symbols).to_contain("simple_2d_fill_u32")
expect(cuda_plan.required_symbols).to_contain("simple_2d_copy_u32")
expect(cuda_plan.required_symbols).to_contain("simple_2d_alpha_u32")
expect(cuda_plan.required_symbols).to_contain("simple_2d_scroll_u32")
expect(hip_plan.required_symbols).to_contain("simple_2d_fill_u32")
expect(hip_plan.required_symbols).to_contain("simple_2d_copy_u32")
expect(hip_plan.required_symbols).to_contain("simple_2d_alpha_u32")
expect(hip_plan.required_symbols).to_contain("simple_2d_scroll_u32")
expect(opencl_plan.required_symbols).to_contain("simple_2d_fill_u32")
expect(opencl_plan.required_symbols).to_contain("simple_2d_copy_u32")
expect(opencl_plan.required_symbols).to_contain("simple_2d_alpha_u32")
expect(opencl_plan.required_symbols).to_contain("simple_2d_scroll_u32")
expect(metal_plan.required_symbols).to_contain("simple_2d_fill_u32")
expect(metal_plan.required_symbols).to_contain("simple_2d_copy_u32")
expect(metal_plan.required_symbols).to_contain("simple_2d_alpha_u32")
```

</details>

#### requires every generated 2D entry before accepting a module binary

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = portable_compute_2d_optimization_compile_plan(PortableComputeTarget.Cuda, "simple_2d_optimization")
val valid = portable_compute_compiled_artifact_evidence(plan, ".version 8.0", ".entry simple_2d_fill_u32 .entry simple_2d_copy_u32 .entry simple_2d_alpha_u32 .entry simple_2d_scroll_u32", 4486)
val missing_scroll = portable_compute_compiled_artifact_evidence(plan, ".version 8.0", ".entry simple_2d_fill_u32 .entry simple_2d_copy_u32 .entry simple_2d_alpha_u32", 4486)

expect(valid.artifact_valid).to_equal(true)
expect(valid.reason).to_equal("pass")
expect(missing_scroll.artifact_valid).to_equal(false)
expect(missing_scroll.reason).to_equal("missing-entry-symbol:simple_2d_scroll_u32")
```

</details>

<details>
<summary>Advanced: builds a smoke matrix for CUDA HIP OpenCL and Metal</summary>

#### builds a smoke matrix for CUDA HIP OpenCL and Metal

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = emit_portable_compute_smoke_matrix()
expect(matrix.len()).to_equal(4)
expect(matrix[0].target_name()).to_equal("cuda")
expect(matrix[1].target_name()).to_equal("hip")
expect(matrix[2].target_name()).to_equal("opencl")
expect(matrix[3].target_name()).to_equal("metal")
expect(matrix[0].source).to_contain("simple_2d_scroll_u32")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/codegen/gpu_portable_compute_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- portable GPU compute emitter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
