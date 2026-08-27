# GPU Kernel Compilation

> Tests that @gpu_kernel functions are properly lowered through HIR -> MIR and compiled to PTX with .entry directives. Validates GPU intrinsic name recognition (thread ID, synchronization, memory, atomic operations), PTX output structure (version, target, address size, directives), special register mappings, and the full compilation pipeline from Simple source to GPU-ready output. No GPU hardware required.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes all thread ID intrinsic names
   - Expected: names[0] equals `gpu_global_id`
   - Expected: names.len() equals `11`
   - Expected: names[1] equals `gpu_global_id_x`
   - Expected: names[2] equals `gpu_global_id_y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes all thread ID intrinsic names")
val names = thread_id_intrinsics()
expect(names[0]).to_equal("gpu_global_id")
expect(names.len()).to_equal(11)
expect(names[1]).to_equal("gpu_global_id_x")
expect(names[2]).to_equal("gpu_global_id_y")
```

</details>

#### recognizes all synchronization intrinsic names

- recognizes all synchronization intrinsic names
   - Expected: names[0] equals `gpu_sync`
   - Expected: names.len() equals `4`
   - Expected: names[1] equals `gpu_barrier`
   - Expected: names[2] equals `gpu_syncthreads`
   - Expected: names[3] equals `gpu_mem_fence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes all synchronization intrinsic names")
val names = sync_intrinsics()
expect(names[0]).to_equal("gpu_sync")
expect(names.len()).to_equal(4)
expect(names[1]).to_equal("gpu_barrier")
expect(names[2]).to_equal("gpu_syncthreads")
expect(names[3]).to_equal("gpu_mem_fence")
```

</details>

#### recognizes all atomic operation intrinsic names

- recognizes all atomic operation intrinsic names
   - Expected: names[0] equals `gpu_atomic_add`
   - Expected: names.len() equals `9`
   - Expected: names[8] equals `gpu_atomic_cas`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes all atomic operation intrinsic names")
val names = atomic_intrinsics()
expect(names[0]).to_equal("gpu_atomic_add")
expect(names.len()).to_equal(9)
expect(names[8]).to_equal("gpu_atomic_cas")
```

</details>

#### recognizes all memory intrinsic names

- recognizes all memory intrinsic names
   - Expected: names[0] equals `gpu_load_f64`
   - Expected: names.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes all memory intrinsic names")
val names = memory_intrinsics()
expect(names[0]).to_equal("gpu_load_f64")
expect(names.len()).to_equal(4)
```

</details>

#### load intrinsics produce global memory PTX

- load intrinsics produce global memory PTX


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("load intrinsics produce global memory PTX")
val ptx_load = "ld.global.f64"
expect(ptx_load).to_contain("global")
expect(ptx_load).to_contain("f64")
```

</details>

#### store intrinsics produce global memory PTX

- store intrinsics produce global memory PTX


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("store intrinsics produce global memory PTX")
val ptx_store = "st.global.f64"
expect(ptx_store).to_contain("global")
```

</details>

#### all intrinsic names start with gpu_ prefix

- all intrinsic names start with gpu_ prefix
   - Expected: all_names.len() equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all intrinsic names start with gpu_ prefix")
val all_names = thread_id_intrinsics() + sync_intrinsics() + atomic_intrinsics() + memory_intrinsics()
# Total: 11 + 4 + 9 + 4 = 28 intrinsics
expect(all_names.len()).to_equal(28)
for name in all_names:
    expect(name).to_start_with("gpu_")
```

</details>

### PTX output structure

#### emits correct PTX version header

- emits correct PTX version header
   - Expected: version equals `.version 8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits correct PTX version header")
val version = expected_ptx_version()
expect(version).to_equal(".version 8.0")
```

</details>

#### emits correct target for SM 8.6 (Ada Lovelace)

- emits correct target for SM 8.6 (Ada Lovelace)
   - Expected: target equals `.target sm_86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits correct target for SM 8.6 (Ada Lovelace)")
val target = expected_ptx_target(8, 6)
expect(target).to_equal(".target sm_86")
```

</details>

#### emits correct target for SM 7.5 (Turing)

- emits correct target for SM 7.5 (Turing)
   - Expected: target equals `.target sm_75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits correct target for SM 7.5 (Turing)")
val target = expected_ptx_target(7, 5)
expect(target).to_equal(".target sm_75")
```

</details>

#### uses 64-bit address size

- uses 64-bit address size
   - Expected: addr equals `.address_size 64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses 64-bit address size")
val addr = expected_ptx_address_size()
expect(addr).to_equal(".address_size 64")
```

</details>

#### uses .entry directive for kernel functions

- uses .entry directive for kernel functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses .entry directive for kernel functions")
val directive = kernel_directive()
expect(directive).to_start_with(".visible")
expect(directive).to_contain(".entry")
```

</details>

#### uses .func directive for device functions

- uses .func directive for device functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses .func directive for device functions")
val directive = device_func_directive()
expect(directive).to_start_with(".visible")
expect(directive).to_contain(".func")
```

</details>

### PTX special registers

#### maps gpu_local_id_x to %tid.x

- maps gpu_local_id_x to %tid.x
   - Expected: ptx_thread_id_x() equals `%tid.x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps gpu_local_id_x to %tid.x")
expect(ptx_thread_id_x()).to_equal("%tid.x")
```

</details>

#### maps gpu_block_id_x to %ctaid.x

- maps gpu_block_id_x to %ctaid.x
   - Expected: ptx_block_id_x() equals `%ctaid.x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps gpu_block_id_x to %ctaid.x")
expect(ptx_block_id_x()).to_equal("%ctaid.x")
```

</details>

#### maps gpu_block_dim_x to %ntid.x

- maps gpu_block_dim_x to %ntid.x
   - Expected: ptx_block_dim_x() equals `%ntid.x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps gpu_block_dim_x to %ntid.x")
expect(ptx_block_dim_x()).to_equal("%ntid.x")
```

</details>

#### maps gpu_grid_dim_x to %nctaid.x

- maps gpu_grid_dim_x to %nctaid.x
   - Expected: ptx_grid_dim_x() equals `%nctaid.x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps gpu_grid_dim_x to %nctaid.x")
expect(ptx_grid_dim_x()).to_equal("%nctaid.x")
```

</details>

### GPU kernel compilation pipeline

#### @gpu_kernel attribute is recognized by parser

- @gpu_kernel attribute is recognized by parser
   - Expected: attr_name equals `gpu_kernel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("@gpu_kernel attribute is recognized by parser")
# FunctionAttr struct has is_gpu_kernel: bool field
# parse_function_attrs checks attr.name == "gpu_kernel"
val attr_name = "gpu_kernel"
expect(attr_name).to_equal("gpu_kernel")
```

</details>

#### pipeline has 5 stages from source to PTX

- pipeline has 5 stages from source to PTX
   - Expected: stages.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pipeline has 5 stages from source to PTX")
val stages = pipeline_stages()
expect(stages[0]).to_contain("@gpu_kernel")
expect(stages.len()).to_equal(5)
expect(stages[4]).to_contain(".entry")
```

</details>

#### MIR instructions include GPU-specific operations

- MIR instructions include GPU-specific operations
   - Expected: mir_gpu_instructions.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MIR instructions include GPU-specific operations")
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

- CudaBackend can be created with compute capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CudaBackend can be created with compute capability")
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

- GpuBarrierScope has Workgroup variant
   - Expected: scope_name equals `Workgroup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GpuBarrierScope has Workgroup variant")
# GpuBarrier(scope: GpuBarrierScope) in MIR
# PTX: bar.sync 0
val scope_name = "Workgroup"
expect(scope_name).to_equal("Workgroup")
```

</details>

#### GpuMemFence has device and system scopes

- GpuMemFence has device and system scopes
   - Expected: scope_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GpuMemFence has device and system scopes")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b56c8e0960e41da1e60c556951b823001e189f7ada9dafd7272113e951c9b2b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b56c8e0960e41da1e60c556951b823001e189f7ada9dafd7272113e951c9b2b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b56c8e0960e41da1e60c556951b823001e189f7ada9dafd7272113e951c9b2b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/gpu_kernel_compilation_spec.spl
mirror: doc/06_spec/03_system/feature/usage/gpu_kernel_compilation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/gpu_kernel_compilation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/gpu_kernel_compilation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/gpu_kernel_compilation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/gpu_kernel_compilation_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes all thread ID intrinsic names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gpu_kernel_compilation_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes all synchronization intrinsic names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gpu_kernel_compilation_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes all atomic operation intrinsic names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
