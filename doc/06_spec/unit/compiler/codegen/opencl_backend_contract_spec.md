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
| 5 | 5 | 0 | 0 |

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/codegen/opencl_backend_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenCL backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
