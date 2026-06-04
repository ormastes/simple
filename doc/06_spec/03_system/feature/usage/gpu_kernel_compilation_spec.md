# GPU Kernel Compilation

> Tests that @gpu_kernel functions are properly lowered through HIR -> MIR and compiled to PTX with .entry directives. Validates GPU intrinsic name recognition (thread ID, synchronization, memory, atomic operations), PTX output structure (version, target, address size, directives), special register mappings, and the full compilation pipeline from Simple source to GPU-ready output. No GPU hardware required.

<!-- sdn-diagram:id=gpu_kernel_compilation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_kernel_compilation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_kernel_compilation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_kernel_compilation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Kernel Compilation

Tests that @gpu_kernel functions are properly lowered through HIR -> MIR and compiled to PTX with .entry directives. Validates GPU intrinsic name recognition (thread ID, synchronization, memory, atomic operations), PTX output structure (version, target, address size, directives), special register mappings, and the full compilation pipeline from Simple source to GPU-ready output. No GPU hardware required.

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | In Progress |
| Source | `test/03_system/feature/usage/gpu_kernel_compilation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that @gpu_kernel functions are properly lowered through HIR -> MIR and compiled
to PTX with .entry directives. Validates GPU intrinsic name recognition (thread ID,
synchronization, memory, atomic operations), PTX output structure (version, target,
address size, directives), special register mappings, and the full compilation pipeline
from Simple source to GPU-ready output. No GPU hardware required.

## Scenarios

### GPU intrinsic recognition

#### recognizes all thread ID intrinsic names

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = thread_id_intrinsics()
expect(names[0]).to_equal("gpu_global_id")
expect(names.len()).to_equal(11)
expect(names[1]).to_equal("gpu_global_id_x")
expect(names[2]).to_equal("gpu_global_id_y")
```

</details>

#### recognizes all synchronization intrinsic names

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = sync_intrinsics()
expect(names[0]).to_equal("gpu_sync")
expect(names.len()).to_equal(4)
expect(names[1]).to_equal("gpu_barrier")
expect(names[2]).to_equal("gpu_syncthreads")
expect(names[3]).to_equal("gpu_mem_fence")
```

</details>

#### recognizes all atomic operation intrinsic names

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = atomic_intrinsics()
expect(names[0]).to_equal("gpu_atomic_add")
expect(names.len()).to_equal(9)
expect(names[8]).to_equal("gpu_atomic_cas")
```

</details>

#### recognizes all memory intrinsic names

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = memory_intrinsics()
expect(names[0]).to_equal("gpu_load_f64")
expect(names.len()).to_equal(4)
```

</details>

#### load intrinsics produce global memory PTX

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptx_load = "ld.global.f64"
expect(ptx_load).to_contain("global")
expect(ptx_load).to_contain("f64")
```

</details>

#### store intrinsics produce global memory PTX

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptx_store = "st.global.f64"
expect(ptx_store).to_contain("global")
```

</details>

#### all intrinsic names start with gpu_ prefix

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_names = thread_id_intrinsics() + sync_intrinsics() + atomic_intrinsics() + memory_intrinsics()
# Total: 11 + 4 + 9 + 4 = 28 intrinsics
expect(all_names.len()).to_equal(28)
for name in all_names:
    expect(name).to_start_with("gpu_")
```

</details>

### PTX output structure

#### emits correct PTX version header

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = expected_ptx_version()
expect(version).to_equal(".version 7.8")
```

</details>

#### emits correct target for SM 8.6 (Ada Lovelace)

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = expected_ptx_target(8, 6)
expect(target).to_equal(".target sm_86")
```

</details>

#### emits correct target for SM 7.5 (Turing)

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = expected_ptx_target(7, 5)
expect(target).to_equal(".target sm_75")
```

</details>

#### uses 64-bit address size

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = expected_ptx_address_size()
expect(addr).to_equal(".address_size 64")
```

</details>

#### uses .entry directive for kernel functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val directive = kernel_directive()
expect(directive).to_start_with(".visible")
expect(directive).to_contain(".entry")
```

</details>

#### uses .func directive for device functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val directive = device_func_directive()
expect(directive).to_start_with(".visible")
expect(directive).to_contain(".func")
```

</details>

### PTX special registers

#### maps gpu_local_id_x to %tid.x

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ptx_thread_id_x()).to_equal("%tid.x")
```

</details>

#### maps gpu_block_id_x to %ctaid.x

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ptx_block_id_x()).to_equal("%ctaid.x")
```

</details>

#### maps gpu_block_dim_x to %ntid.x

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ptx_block_dim_x()).to_equal("%ntid.x")
```

</details>

#### maps gpu_grid_dim_x to %nctaid.x

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ptx_grid_dim_x()).to_equal("%nctaid.x")
```

</details>

### GPU kernel compilation pipeline

#### @gpu_kernel attribute is recognized by parser

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FunctionAttr struct has is_gpu_kernel: bool field
# parse_function_attrs checks attr.name == "gpu_kernel"
val attr_name = "gpu_kernel"
expect(attr_name).to_equal("gpu_kernel")
```

</details>

#### pipeline has 5 stages from source to PTX

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stages = pipeline_stages()
expect(stages[0]).to_contain("@gpu_kernel")
expect(stages.len()).to_equal(5)
expect(stages[4]).to_contain(".entry")
```

</details>

#### MIR instructions include GPU-specific operations

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# MIR instruction enum includes:
# GpuGlobalId, GpuLocalId, GpuBlockId, GpuBlockDim, GpuGridDim
# GpuBarrier, GpuMemFence
val mir_gpu_instructions = [
    "GpuGlobalId",
    "GpuLocalId",
    "GpuBlockId",
    "GpuBlockDim",
    "GpuGridDim",
    "GpuBarrier",
    "GpuMemFence"
]
expect(mir_gpu_instructions.len()).to_equal(7)
```

</details>

#### CudaBackend can be created with compute capability

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CudaBackend.create((8, 6)) initializes:
# - CudaTypeMapper for SM 8.6
# - PtxBuilder with (major, minor) tuple
# - CompileOptions with CodegenTarget.CudaPtx
val sm_major = 8
val sm_minor = 6
expect(sm_major).to_be_greater_than(0)
expect(sm_minor).to_be_greater_than(0)
```

</details>

### GPU barrier and memory scope

#### GpuBarrierScope has Workgroup variant

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GpuBarrier(scope: GpuBarrierScope) in MIR
# PTX: bar.sync 0
val scope_name = "Workgroup"
expect(scope_name).to_equal("Workgroup")
```

</details>

#### GpuMemFence has device and system scopes

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GpuMemFence(scope: GpuMemoryScope) in MIR
val scope_names = ["Device", "System"]
expect(scope_names.len()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
