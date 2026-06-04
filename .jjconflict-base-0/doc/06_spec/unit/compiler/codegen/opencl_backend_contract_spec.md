# Opencl Backend Contract Specification

> <details>

<!-- sdn-diagram:id=opencl_backend_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=opencl_backend_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

opencl_backend_contract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=opencl_backend_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opencl Backend Contract Specification

## Scenarios

### OpenCL backend contract

#### names the OpenCL backend and supports OpenCL artifact targets only

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = OpenClBackend.create(compileoptions_default_options())

expect(backend.backend_name()).to_equal("opencl")
expect(backend.supports_target(CodegenTarget.OpenClC)).to_equal(true)
expect(backend.supports_target(CodegenTarget.OpenClSpirv)).to_equal(true)
expect(backend.supports_target(CodegenTarget.CudaPtx)).to_equal(false)
expect(backend.output_kind() == CodegenOutputKind.GpuCode).to_equal(true)
```

</details>

#### builds generated Engine2D OpenCL C to SPIR-V artifact evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exported = "OpEntryPoint GLCompute %simple_2d_fill_u32 \"simple_2d_fill_u32\" OpEntryPoint GLCompute %simple_2d_copy_u32 \"simple_2d_copy_u32\" OpEntryPoint GLCompute %simple_2d_alpha_u32 \"simple_2d_alpha_u32\" OpEntryPoint GLCompute %simple_2d_scroll_u32 \"simple_2d_scroll_u32\""
val contract = opencl_backend_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.5", exported, 4096)

expect(contract.ready).to_equal(true)
expect(contract.status).to_equal("compiled_artifact_verified")
expect(contract.plan.source_format).to_equal("opencl-c")
expect(contract.plan.binary_format).to_equal("spirv")
expect(contract.plan.artifact_path_suffix).to_equal("simple_2d_optimization.spirv")
expect(contract.source).to_contain("__kernel void simple_2d_fill_u32")
expect(contract.source).to_contain("__kernel void simple_2d_scroll_u32")
expect(contract.summary()).to_contain("ready=true")
```

</details>

#### rejects incomplete OpenCL generated artifact evidence

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exported = "OpEntryPoint GLCompute %simple_2d_fill_u32 \"simple_2d_fill_u32\" OpEntryPoint GLCompute %simple_2d_copy_u32 \"simple_2d_copy_u32\" OpEntryPoint GLCompute %simple_2d_alpha_u32 \"simple_2d_alpha_u32\""
val contract = opencl_backend_2d_compile_contract("simple_2d_optimization", "SPIR-V 1.5", exported, 4096)

expect(contract.ready).to_equal(false)
expect(contract.status).to_equal("missing-entry-symbol:simple_2d_scroll_u32")
expect(contract.diagnostic).to_contain("OpenCL artifact rejected")
```

</details>

#### plans MIR kernels using OpenCL target metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opencl_kernel = make_kernel_function(1, "opencl_kernel", "opencl")
val auto_kernel = make_kernel_function(2, "auto_kernel", "auto")
val cuda_kernel = make_kernel_function(3, "cuda_kernel", "cuda")
val module = make_kernel_module([opencl_kernel, auto_kernel, cuda_kernel])

val plan = OpenClBackend.plan_module_kernels(module)

expect(OpenClBackend.accepts_gpu_kernel(opencl_kernel)).to_equal(true)
expect(OpenClBackend.accepts_gpu_kernel(auto_kernel)).to_equal(true)
expect(OpenClBackend.accepts_gpu_kernel(cuda_kernel)).to_equal(false)
expect(plan.accepted_kernel_count).to_equal(2)
expect(plan.rejected_kernel_count).to_equal(1)
expect(plan.diagnostic).to_contain("cuda_kernel")
```

</details>

#### emits OpenCL C source for accepted MIR GPU kernel subset

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_id_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_id_kernel")
expect(source).to_contain("ulong v0 = get_global_id(0);")
expect(source).to_contain("ulong v1 = get_local_id(0);")
expect(source).to_contain("barrier(CLK_LOCAL_MEM_FENCE);")
expect(source).to_contain("return;")
```

</details>

#### emits OpenCL C load store and pointer arithmetic for memory kernels

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_vector_add_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_vector_add_u32(__global uint* a, __global uint* b, __global uint* out)")
expect(source).to_contain("ulong v3 = get_global_id(0);")
expect(source).to_contain("__global uint* v4 = (a + v3);")
expect(source).to_contain("__global uint* v5 = (b + v3);")
expect(source).to_contain("uint v7 = *v4;")
expect(source).to_contain("uint v8 = *v5;")
expect(source).to_contain("uint v9 = v7 + v8;")
expect(source).to_contain("__global uint* v6 = (out + v3);")
expect(source).to_contain("*v6 = v9;")
```

</details>

#### emits OpenCL C checked arithmetic as GPU arithmetic

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_checked_binop_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_checked_add_u32(uint left, uint right)")
expect(source).to_contain("uint v2 = left + right;")
expect(source).to_contain("return;")
```

</details>

#### emits OpenCL C casts and bitcasts distinctly

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_cast_bitcast_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_cast_bitcast_u32(uint bits)")
expect(source).to_contain("float v1 = (float)(bits);")
expect(source).to_contain("float v2 = as_float(bits);")
expect(source).to_contain("return;")
```

</details>

#### emits OpenCL C direct named device calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_scale_device_function(), make_opencl_call_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("uint opencl_scale_u32(uint left, uint right)")
expect(source).to_contain("uint v2 = left * right;")
expect(source).to_contain("return v2;")
expect(source).to_contain("__kernel void opencl_call_u32(uint left, uint right)")
expect(source).to_contain("uint v2 = opencl_scale_u32(left, right);")
expect(source).to_contain("return;")
```

</details>

#### emits OpenCL C array aggregates and field access

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_array_aggregate_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_array_aggregate_u32(uint a, uint b, uint c)")
expect(source).to_contain("uint v3[3] = { a, b, c };")
expect(source).to_contain("uint v4 = v3[1];")
expect(source).to_contain("v3[2] = v4;")
expect(source).to_contain("return;")
```

</details>

#### emits OpenCL C private allocation for per-work-item locals

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_alloc_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_private_alloc_u32(uint value)")
expect(source).to_contain("__private uint v1_slot; __private uint* v1 = &v1_slot;")
expect(source).to_contain("*v1 = value;")
expect(source).to_contain("uint v2 = *v1;")
expect(source).to_contain("return;")
```

</details>

#### maps Simple SIMD vector types to OpenCL C vector types

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(OpenClBackend.opencl_type(vec4f_type(), false)).to_equal("float4")
expect(OpenClBackend.opencl_type(vec8f_type(), false)).to_equal("float8")
expect(OpenClBackend.opencl_type(vec4d_type(), false)).to_equal("double4")
expect(OpenClBackend.opencl_type(vec4i_type(), false)).to_equal("int4")
expect(OpenClBackend.opencl_type(vec8i_type(), false)).to_equal("int8")
```

</details>

#### emits OpenCL C SIMD vector arithmetic and f32x4 reductions

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_simd_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_simd_vectors(float4 x, float4 y, float4 z, int4 ix, int4 iy)")
expect(source).to_contain("float4 v5 = x + y;")
expect(source).to_contain("float4 v6 = fma(v5, y, z);")
expect(source).to_contain("int4 v7 = ix ^ iy;")
expect(source).to_contain("int4 v8 = v7 & iy;")
expect(source).to_contain("float v9 = v6.s0 + v6.s1 + v6.s2 + v6.s3;")
expect(source).to_contain("float v10 = fmax(fmax(v6.s0, v6.s1), fmax(v6.s2, v6.s3));")
expect(source).to_contain("float v11 = fmin(fmin(v6.s0, v6.s1), fmin(v6.s2, v6.s3));")
expect(source).to_contain("return;")
```

</details>

#### emits OpenCL C labels gotos and conditional branches

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_branch_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_branch_kernel(bool flag)")
expect(source).to_contain("BB0:")
expect(source).to_contain("if (flag) { goto BB1; } else { goto BB2; }")
expect(source).to_contain("BB1:")
expect(source).to_contain("goto BB3;")
expect(source).to_contain("BB2:")
expect(source).to_contain("BB3:")
expect(source).to_contain("return;")
```

</details>

#### emits OpenCL C switch terminators with case and default gotos

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_switch_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_switch_kernel(uint selector)")
expect(source).to_contain("switch (selector)")
expect(source).to_contain("case 1")
expect(source).to_contain("case 2")
expect(source).to_contain("default")
expect(source).to_contain("goto")
```

</details>

#### emits OpenCL C atomics fences and local memory for GPU kernels

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_kernel_module([make_opencl_atomic_kernel()])
val source = OpenClBackend.compile_module_to_opencl_source(module).unwrap()

expect(source).to_contain("__kernel void opencl_atomic_u32(__global uint* accum, uint value)")
expect(source).to_contain("uint v2 = atomic_add(accum, value);")
expect(source).to_contain("uint v3 = atomic_cmpxchg(accum, value, v2);")
expect(source).to_contain("mem_fence(CLK_LOCAL_MEM_FENCE | CLK_GLOBAL_MEM_FENCE);")
expect(source).to_contain("__local uint v4[32];")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/opencl_backend_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenCL backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
