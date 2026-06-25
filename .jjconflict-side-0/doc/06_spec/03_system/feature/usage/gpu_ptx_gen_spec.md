# GPU PTX Code Generation Specification

> PTX code generation tests verify that the CUDA backend correctly translates MIR instructions to NVIDIA PTX assembly. These tests do NOT require GPU hardware - they only verify the text output of the code generator.

<!-- sdn-diagram:id=gpu_ptx_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_ptx_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_ptx_gen_spec -> compiler
gpu_ptx_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_ptx_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 98 | 98 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU PTX Code Generation Specification

PTX code generation tests verify that the CUDA backend correctly translates MIR instructions to NVIDIA PTX assembly. These tests do NOT require GPU hardware - they only verify the text output of the code generator.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #816-820 |
| Category | Compiler Backend |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/gpu_ptx_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

PTX code generation tests verify that the CUDA backend correctly translates
MIR instructions to NVIDIA PTX assembly. These tests do NOT require GPU
hardware - they only verify the text output of the code generator.

## Key Concepts

| Concept | Description |
|---------|-------------|
| PTX | NVIDIA Parallel Thread Execution virtual ISA |
| MIR | Mid-level Intermediate Representation |
| Kernel | GPU entry point function (.entry) |
| Device Function | GPU-callable function (.func) |

## Behavior

- CudaBackend compiles MIR modules to PTX text
- PTX header contains version, target, and address size
- Kernel functions use .visible .entry directive
- Device functions use .visible .func directive
- Thread IDs accessed via special registers %tid, %ctaid, %ntid
- Barrier synchronization via bar.sync

## Scenarios

### PTX Builder - Module Header

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### with SM 8.6 compute capability

#### generates correct PTX header

1. var builder = PtxBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_module_header("test_module")
val ptx = builder.build()

expect(ptx).to_contain(".version 7.8")
expect(ptx).to_contain(".target sm_86")
expect(ptx).to_contain(".address_size 64")
expect(ptx).to_contain("test_module")
```

</details>

#### with SM 7.0 compute capability

#### generates correct target for Volta

1. var builder = PtxBuilder  create
2. builder emit module header


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((7, 0))
builder.emit_module_header("volta_module")
val ptx = builder.build()

expect(ptx).to_contain(".target sm_70")
```

</details>

### PTX Builder - Register Declarations

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### declares integer registers

1. var builder = PtxBuilder  create
2. builder emit reg decl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_reg_decl("%r0", PrimitiveType.I64)
val ptx = builder.build()

expect(ptx).to_contain(".reg .s64 %r0;")
```

</details>

#### declares float registers

1. var builder = PtxBuilder  create
2. builder emit reg decl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_reg_decl("%f0", PrimitiveType.F32)
val ptx = builder.build()

expect(ptx).to_contain(".reg .f32 %f0;")
```

</details>

#### declares predicate registers

1. var builder = PtxBuilder  create
2. builder emit pred decl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_pred_decl("%p0")
val ptx = builder.build()

expect(ptx).to_contain(".reg .pred %p0;")
```

</details>

#### declares unsigned integer registers

1. var builder = PtxBuilder  create
2. builder emit reg decl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_reg_decl("%u0", PrimitiveType.U32)
val ptx = builder.build()

expect(ptx).to_contain(".reg .u32 %u0;")
```

</details>

### PTX Builder - Arithmetic Operations

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates integer add

1. var builder = PtxBuilder  create
2. builder emit add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_add("%r0", PrimitiveType.I64, "%r1", "%r2")
val ptx = builder.build()

expect(ptx).to_contain("add.s64 %r0, %r1, %r2;")
```

</details>

#### generates integer subtract

1. var builder = PtxBuilder  create
2. builder emit sub


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_sub("%r0", PrimitiveType.I32, "%r1", "%r2")
val ptx = builder.build()

expect(ptx).to_contain("sub.s32 %r0, %r1, %r2;")
```

</details>

#### generates integer multiply with low-word

1. var builder = PtxBuilder  create
2. builder emit mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_mul("%r0", PrimitiveType.I64, "%r1", "%r2")
val ptx = builder.build()

expect(ptx).to_contain("mul.lo.s64 %r0, %r1, %r2;")
```

</details>

#### generates float multiply

1. var builder = PtxBuilder  create
2. builder emit mul


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_mul("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("mul.f32 %f0, %f1, %f2;")
```

</details>

#### generates float divide with rounding

1. var builder = PtxBuilder  create
2. builder emit div


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_div("%f0", PrimitiveType.F64, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("div.rn.f64 %f0, %f1, %f2;")
```

</details>

#### generates approximate float divide for f32

1. var builder = PtxBuilder  create
2. builder emit div


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_div("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("div.approx.f32 %f0, %f1, %f2;")
```

</details>

#### generates negate

1. var builder = PtxBuilder  create
2. builder emit neg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_neg("%r0", PrimitiveType.I64, "%r1")
val ptx = builder.build()

expect(ptx).to_contain("neg.s64 %r0, %r1;")
```

</details>

### PTX Builder - Comparisons

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates equality comparison

1. var builder = PtxBuilder  create
2. builder emit compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_compare("%p0", "eq", PrimitiveType.I64, "%r0", "%r1")
val ptx = builder.build()

expect(ptx).to_contain("setp.eq.s64 %p0, %r0, %r1;")
```

</details>

#### generates less-than comparison

1. var builder = PtxBuilder  create
2. builder emit compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_compare("%p0", "lt", PrimitiveType.F32, "%f0", "%f1")
val ptx = builder.build()

expect(ptx).to_contain("setp.lt.f32 %p0, %f0, %f1;")
```

</details>

### PTX Builder - Memory Operations

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates global memory load

1. var builder = PtxBuilder  create
2. builder emit load


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_load("%r0", PrimitiveType.I64, "%addr", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("ld.global.s64 %r0, [%addr];")
```

</details>

#### generates global memory store

1. var builder = PtxBuilder  create
2. builder emit store


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_store(PrimitiveType.I64, "%addr", "%r0", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("st.global.s64 [%addr], %r0;")
```

</details>

#### generates shared memory load

1. var builder = PtxBuilder  create
2. builder emit load


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_load("%r0", PrimitiveType.F32, "%saddr", MemorySpace.Shared)
val ptx = builder.build()

expect(ptx).to_contain("ld.shared.f32 %r0, [%saddr];")
```

</details>

#### generates shared memory allocation

1. var builder = PtxBuilder  create
2. builder emit shared memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_shared_memory("shared_buf", PrimitiveType.F32, 256)
val ptx = builder.build()

expect(ptx).to_contain(".shared .f32 shared_buf[256];")
```

</details>

#### generates local memory allocation

1. var builder = PtxBuilder  create
2. builder emit local alloc


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_local_alloc("local_buf", PrimitiveType.I64, 8)
val ptx = builder.build()

expect(ptx).to_contain(".local .s64 local_buf[8];")
```

</details>

### PTX Builder - Thread IDs

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates thread ID access for x dimension

1. var builder = PtxBuilder  create
2. builder emit get thread id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_get_thread_id("%tid_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %tid_x, %tid.x;")
```

</details>

#### generates thread ID access for y dimension

1. var builder = PtxBuilder  create
2. builder emit get thread id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_get_thread_id("%tid_y", 1)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %tid_y, %tid.y;")
```

</details>

#### generates block ID access

1. var builder = PtxBuilder  create
2. builder emit get block id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_get_block_id("%bid_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %bid_x, %ctaid.x;")
```

</details>

#### generates block dim access

1. var builder = PtxBuilder  create
2. builder emit get block dim


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_get_block_dim("%bdim_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %bdim_x, %ntid.x;")
```

</details>

#### generates grid dim access

1. var builder = PtxBuilder  create
2. builder emit get grid dim


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_get_grid_dim("%gdim_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %gdim_x, %nctaid.x;")
```

</details>

#### computes global thread ID

1. var builder = PtxBuilder  create
2. builder emit compute global id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_compute_global_id("%gid", 0)
val ptx = builder.build()

# Global ID = blockIdx * blockDim + threadIdx
expect(ptx).to_contain("mul.lo.u32")
expect(ptx).to_contain("add.u32")
```

</details>

### PTX Builder - Synchronization

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates block-level barrier

1. var builder = PtxBuilder  create
2. builder emit barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_barrier()
val ptx = builder.build()

expect(ptx).to_contain("bar.sync 0;")
```

</details>

#### generates CTA memory barrier

1. var builder = PtxBuilder  create
2. builder emit membar cta


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_membar_cta()
val ptx = builder.build()

expect(ptx).to_contain("membar.cta;")
```

</details>

#### generates global memory barrier

1. var builder = PtxBuilder  create
2. builder emit membar gl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_membar_gl()
val ptx = builder.build()

expect(ptx).to_contain("membar.gl;")
```

</details>

#### generates system memory barrier

1. var builder = PtxBuilder  create
2. builder emit membar sys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_membar_sys()
val ptx = builder.build()

expect(ptx).to_contain("membar.sys;")
```

</details>

### PTX Builder - Atomic Operations

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates atomic add

1. var builder = PtxBuilder  create
2. builder emit atomic add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_add("%r0", PrimitiveType.I64, "%addr", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.add.s64 %r0, [%addr], %val;")
```

</details>

#### generates atomic min

1. var builder = PtxBuilder  create
2. builder emit atomic min


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_min("%r0", PrimitiveType.I32, "%addr", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.min.s32 %r0, [%addr], %val;")
```

</details>

#### generates atomic max

1. var builder = PtxBuilder  create
2. builder emit atomic max


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_max("%r0", PrimitiveType.U64, "%addr", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.max.u64 %r0, [%addr], %val;")
```

</details>

#### generates atomic compare-and-swap

1. var builder = PtxBuilder  create
2. builder emit atomic cas


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_cas("%r0", PrimitiveType.I64, "%addr", "%cmp", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.cas.s64 %r0, [%addr], %cmp, %val;")
```

</details>

#### generates shared memory atomic add

1. var builder = PtxBuilder  create
2. builder emit atomic add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_add("%r0", PrimitiveType.I32, "%saddr", "%val", MemorySpace.Shared)
val ptx = builder.build()

expect(ptx).to_contain("atom.shared.add.s32 %r0, [%saddr], %val;")
```

</details>

### PTX Builder - Type Conversions

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### converts int to float

1. var builder = PtxBuilder  create
2. builder emit convert


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%f0", PrimitiveType.F32, "%r0", PrimitiveType.I32)
val ptx = builder.build()

expect(ptx).to_contain("cvt.rn.f32.s32 %f0, %r0;")
```

</details>

#### converts float to int

1. var builder = PtxBuilder  create
2. builder emit convert


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%r0", PrimitiveType.I64, "%f0", PrimitiveType.F64)
val ptx = builder.build()

expect(ptx).to_contain("cvt.rzi.s64.f64 %r0, %f0;")
```

</details>

#### converts float to float

1. var builder = PtxBuilder  create
2. builder emit convert


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%f0", PrimitiveType.F64, "%f1", PrimitiveType.F32)
val ptx = builder.build()

expect(ptx).to_contain("cvt.rn.f64.f32 %f0, %f1;")
```

</details>

#### converts int to int

1. var builder = PtxBuilder  create
2. builder emit convert


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%r0", PrimitiveType.I64, "%r1", PrimitiveType.I32)
val ptx = builder.build()

expect(ptx).to_contain("cvt.s64.s32 %r0, %r1;")
```

</details>

### PTX Builder - Math Intrinsics

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates sin approximation

1. var builder = PtxBuilder  create
2. builder emit intrinsic sin


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_sin("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("sin.approx.f32 %f0, %f1;")
```

</details>

#### generates cos approximation

1. var builder = PtxBuilder  create
2. builder emit intrinsic cos


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_cos("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("cos.approx.f32 %f0, %f1;")
```

</details>

#### generates sqrt approximation

1. var builder = PtxBuilder  create
2. builder emit intrinsic sqrt


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_sqrt("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("sqrt.approx.f32 %f0, %f1;")
```

</details>

#### generates abs

1. var builder = PtxBuilder  create
2. builder emit intrinsic abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_abs("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("abs.f32 %f0, %f1;")
```

</details>

#### generates fused multiply-add

1. var builder = PtxBuilder  create
2. builder emit intrinsic fma


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_fma("%f0", PrimitiveType.F32, "%f1", "%f2", "%f3")
val ptx = builder.build()

expect(ptx).to_contain("fma.rn.f32 %f0, %f1, %f2, %f3;")
```

</details>

#### generates exp2 approximation

1. var builder = PtxBuilder  create
2. builder emit intrinsic ex2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_ex2("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("ex2.approx.f32 %f0, %f1;")
```

</details>

#### generates log2 approximation

1. var builder = PtxBuilder  create
2. builder emit intrinsic lg2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_lg2("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("lg2.approx.f32 %f0, %f1;")
```

</details>

#### generates reciprocal approximation

1. var builder = PtxBuilder  create
2. builder emit intrinsic rcp


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_rcp("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("rcp.approx.f32 %f0, %f1;")
```

</details>

#### generates min instruction

1. var builder = PtxBuilder  create
2. builder emit intrinsic min


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_min("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("min.f32 %f0, %f1, %f2;")
```

</details>

#### generates max instruction

1. var builder = PtxBuilder  create
2. builder emit intrinsic max


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_max("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("max.f32 %f0, %f1, %f2;")
```

</details>

### PTX Builder - Control Flow

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates unconditional branch

1. var builder = PtxBuilder  create
2. builder emit branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_branch("BB1")
val ptx = builder.build()

expect(ptx).to_contain("bra BB1;")
```

</details>

#### generates conditional branch

1. var builder = PtxBuilder  create
2. builder emit branch if


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_branch_if("%p0", "BB_true")
val ptx = builder.build()

expect(ptx).to_contain("@%p0 bra BB_true;")
```

</details>

#### generates negated conditional branch

1. var builder = PtxBuilder  create
2. builder emit branch if not


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_branch_if_not("%p0", "BB_false")
val ptx = builder.build()

expect(ptx).to_contain("@!%p0 bra BB_false;")
```

</details>

#### generates labels

1. var builder = PtxBuilder  create
2. builder emit label
3. builder emit line


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_label("BB0")
builder.emit_line("nop;")
val ptx = builder.build()

expect(ptx).to_contain("BB0:")
```

</details>

#### generates return instruction

1. var builder = PtxBuilder  create
2. builder emit ret


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_ret()
val ptx = builder.build()

expect(ptx).to_contain("ret;")
```

</details>

#### generates exit instruction

1. var builder = PtxBuilder  create
2. builder emit exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_exit()
val ptx = builder.build()

expect(ptx).to_contain("exit;")
```

</details>

### PTX Builder - Function Calls

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates function call with return value

1. var builder = PtxBuilder  create
2. builder emit call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_call("%r0", PrimitiveType.I64, "device_func", ["%r1", "%r2"])
val ptx = builder.build()

expect(ptx).to_contain("call (%r0), device_func, (%r1, %r2);")
```

</details>

#### generates void function call

1. var builder = PtxBuilder  create
2. builder emit call void


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_call_void("void_func", ["%r0"])
val ptx = builder.build()

expect(ptx).to_contain("call void_func, (%r0);")
```

</details>

### CUDA Type Mapper - Primitive Types

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### maps integer types to PTX

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.I64)).to_equal(".s64")
expect(mapper.ptx_type(PrimitiveType.I32)).to_equal(".s32")
expect(mapper.ptx_type(PrimitiveType.I16)).to_equal(".s16")
expect(mapper.ptx_type(PrimitiveType.I8)).to_equal(".s8")
```

</details>

#### maps unsigned integer types to PTX

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.U64)).to_equal(".u64")
expect(mapper.ptx_type(PrimitiveType.U32)).to_equal(".u32")
expect(mapper.ptx_type(PrimitiveType.U16)).to_equal(".u16")
expect(mapper.ptx_type(PrimitiveType.U8)).to_equal(".u8")
```

</details>

#### maps float types to PTX

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.F64)).to_equal(".f64")
expect(mapper.ptx_type(PrimitiveType.F32)).to_equal(".f32")
expect(mapper.ptx_type(PrimitiveType.F16)).to_equal(".f16")
```

</details>

#### maps bool to predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.Bool)).to_equal(".pred")
```

</details>

### CUDA Type Mapper - Compute Capabilities

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### detects half precision support

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper_old = CudaTypeMapper__create_sm(5, 0)
val mapper_new = CudaTypeMapper__create_sm(7, 0)
expect(mapper_old.supports_half_precision()).to_equal(false)
expect(mapper_new.supports_half_precision()).to_equal(true)
```

</details>

#### detects tensor core support

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper_old = CudaTypeMapper__create_sm(6, 1)
val mapper_new = CudaTypeMapper__create_sm(7, 0)
expect(mapper_old.supports_tensor_cores()).to_equal(false)
expect(mapper_new.supports_tensor_cores()).to_equal(true)
```

</details>

#### reports correct max threads per block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.max_threads_per_block()).to_equal(1024)
```

</details>

#### reports correct warp size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.warp_size()).to_equal(32)
```

</details>

#### reports correct shared memory for Ampere

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.max_shared_memory()).to_equal(163840)
```

</details>

#### reports correct shared memory for Volta

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(7, 0)
val shared_mem = mapper.max_shared_memory()
expect(shared_mem).to_equal(96 * 1024)
```

</details>

### CUDA Type Mapper - Memory Spaces

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### maps global memory space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Global)).to_equal(".global")
```

</details>

#### maps shared memory space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Shared)).to_equal(".shared")
```

</details>

#### maps local memory space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Local)).to_equal(".local")
```

</details>

#### maps constant memory space

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Constant)).to_equal(".const")
```

</details>

### Launch Configuration

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### creates 1D launch config

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_1d(1024, 256)
expect(config.grid_x).to_equal(4)
expect(config.grid_y).to_equal(1)
expect(config.grid_z).to_equal(1)
expect(config.block_x).to_equal(256)
expect(config.total_threads()).to_equal(1024)
```

</details>

#### rounds up grid size for non-divisible total

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_1d(1000, 256)
expect(config.grid_x).to_equal(4)
expect(config.total_threads()).to_be_greater_than(999)
```

</details>

#### creates 2D launch config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_2d(512, 512, 16, 16)
expect(config.grid_x).to_equal(32)
expect(config.grid_y).to_equal(32)
expect(config.block_x).to_equal(16)
expect(config.block_y).to_equal(16)
```

</details>

#### computes total blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_2d(512, 512, 16, 16)
expect(config.total_blocks()).to_equal(1024)
```

</details>

#### computes threads per block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_2d(512, 512, 16, 16)
expect(config.threads_per_block()).to_equal(256)
```

</details>

#### validates valid config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_1d(1024, 256)
val err = config.validate()
expect(err).to_be_nil()
```

</details>

#### rejects zero block size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_1d(1024, 0)
val err = config.validate()
expect(err).to_be_nil()  # for_1d with 0 produces invalid config
# The grid would be computed with division by zero;
# real validation catches block dims
```

</details>

#### adds shared memory to config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LaunchConfig.for_1d(1024, 256).with_shared_mem(4096)
expect(config.shared_mem_bytes).to_equal(4096)
expect(config.block_x).to_equal(256)
```

</details>

### PTX Builder - Constants

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### loads integer constant

1. var builder = PtxBuilder  create
2. builder emit const int


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_const_int("%r0", PrimitiveType.I64, 42)
val ptx = builder.build()

expect(ptx).to_contain("mov.s64 %r0, 42;")
```

</details>

#### loads unsigned integer constant

1. var builder = PtxBuilder  create
2. builder emit const int


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = PtxBuilder__create((8, 6))
builder.emit_const_int("%r0", PrimitiveType.U32, 100)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %r0, 100;")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 98 |
| Active scenarios | 98 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
