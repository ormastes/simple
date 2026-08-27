# GPU PTX Code Generation Specification

> PTX code generation tests verify that the CUDA backend correctly translates MIR instructions to NVIDIA PTX assembly. These tests do NOT require GPU hardware - they only verify the text output of the code generator.

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
| Updated | 2026-08-26 |
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

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### with SM 8.6 compute capability

#### generates correct PTX header

- generates correct PTX header


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates correct PTX header")
var builder = PtxBuilder__create((8, 6))
builder.emit_module_header("test_module")
val ptx = builder.build()

expect(ptx).to_contain(".version 8.0")
expect(ptx).to_contain(".target sm_86")
expect(ptx).to_contain(".address_size 64")
expect(ptx).to_contain("test_module")
```

</details>

#### with SM 7.0 compute capability

#### generates correct target for Volta

- generates correct target for Volta


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates correct target for Volta")
var builder = PtxBuilder__create((7, 0))
builder.emit_module_header("volta_module")
val ptx = builder.build()

expect(ptx).to_contain(".target sm_70")
```

</details>

### PTX Builder - Register Declarations

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### declares integer registers

- declares integer registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares integer registers")
var builder = PtxBuilder__create((8, 6))
builder.emit_reg_decl("%r0", PrimitiveType.I64)
val ptx = builder.build()

expect(ptx).to_contain(".reg .s64 %r0;")
```

</details>

#### declares float registers

- declares float registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares float registers")
var builder = PtxBuilder__create((8, 6))
builder.emit_reg_decl("%f0", PrimitiveType.F32)
val ptx = builder.build()

expect(ptx).to_contain(".reg .f32 %f0;")
```

</details>

#### declares predicate registers

- declares predicate registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares predicate registers")
var builder = PtxBuilder__create((8, 6))
builder.emit_pred_decl("%p0")
val ptx = builder.build()

expect(ptx).to_contain(".reg .pred %p0;")
```

</details>

#### declares unsigned integer registers

- declares unsigned integer registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares unsigned integer registers")
var builder = PtxBuilder__create((8, 6))
builder.emit_reg_decl("%u0", PrimitiveType.U32)
val ptx = builder.build()

expect(ptx).to_contain(".reg .u32 %u0;")
```

</details>

### PTX Builder - Arithmetic Operations

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates integer add

- generates integer add


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates integer add")
var builder = PtxBuilder__create((8, 6))
builder.emit_add("%r0", PrimitiveType.I64, "%r1", "%r2")
val ptx = builder.build()

expect(ptx).to_contain("add.s64 %r0, %r1, %r2;")
```

</details>

#### generates integer subtract

- generates integer subtract


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates integer subtract")
var builder = PtxBuilder__create((8, 6))
builder.emit_sub("%r0", PrimitiveType.I32, "%r1", "%r2")
val ptx = builder.build()

expect(ptx).to_contain("sub.s32 %r0, %r1, %r2;")
```

</details>

#### generates integer multiply with low-word

- generates integer multiply with low-word


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates integer multiply with low-word")
var builder = PtxBuilder__create((8, 6))
builder.emit_mul("%r0", PrimitiveType.I64, "%r1", "%r2")
val ptx = builder.build()

expect(ptx).to_contain("mul.lo.s64 %r0, %r1, %r2;")
```

</details>

#### generates float multiply

- generates float multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates float multiply")
var builder = PtxBuilder__create((8, 6))
builder.emit_mul("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("mul.f32 %f0, %f1, %f2;")
```

</details>

#### generates float divide with rounding

- generates float divide with rounding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates float divide with rounding")
var builder = PtxBuilder__create((8, 6))
builder.emit_div("%f0", PrimitiveType.F64, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("div.rn.f64 %f0, %f1, %f2;")
```

</details>

#### generates approximate float divide for f32

- generates approximate float divide for f32


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates approximate float divide for f32")
var builder = PtxBuilder__create((8, 6))
builder.emit_div("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("div.approx.f32 %f0, %f1, %f2;")
```

</details>

#### generates negate

- generates negate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates negate")
var builder = PtxBuilder__create((8, 6))
builder.emit_neg("%r0", PrimitiveType.I64, "%r1")
val ptx = builder.build()

expect(ptx).to_contain("neg.s64 %r0, %r1;")
```

</details>

### PTX Builder - Comparisons

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates equality comparison

- generates equality comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates equality comparison")
var builder = PtxBuilder__create((8, 6))
builder.emit_compare("%p0", "eq", PrimitiveType.I64, "%r0", "%r1")
val ptx = builder.build()

expect(ptx).to_contain("setp.eq.s64 %p0, %r0, %r1;")
```

</details>

#### generates less-than comparison

- generates less-than comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates less-than comparison")
var builder = PtxBuilder__create((8, 6))
builder.emit_compare("%p0", "lt", PrimitiveType.F32, "%f0", "%f1")
val ptx = builder.build()

expect(ptx).to_contain("setp.lt.f32 %p0, %f0, %f1;")
```

</details>

### PTX Builder - Memory Operations

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates global memory load

- generates global memory load


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates global memory load")
var builder = PtxBuilder__create((8, 6))
builder.emit_load("%r0", PrimitiveType.I64, "%addr", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("ld.global.s64 %r0, [%addr];")
```

</details>

#### generates global memory store

- generates global memory store


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates global memory store")
var builder = PtxBuilder__create((8, 6))
builder.emit_store(PrimitiveType.I64, "%addr", "%r0", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("st.global.s64 [%addr], %r0;")
```

</details>

#### generates shared memory load

- generates shared memory load


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates shared memory load")
var builder = PtxBuilder__create((8, 6))
builder.emit_load("%r0", PrimitiveType.F32, "%saddr", MemorySpace.Shared)
val ptx = builder.build()

expect(ptx).to_contain("ld.shared.f32 %r0, [%saddr];")
```

</details>

#### generates shared memory allocation

- generates shared memory allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates shared memory allocation")
var builder = PtxBuilder__create((8, 6))
builder.emit_shared_memory("shared_buf", PrimitiveType.F32, 256)
val ptx = builder.build()

expect(ptx).to_contain(".shared .f32 shared_buf[256];")
```

</details>

#### generates local memory allocation

- generates local memory allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates local memory allocation")
var builder = PtxBuilder__create((8, 6))
builder.emit_local_alloc("local_buf", PrimitiveType.I64, 8)
val ptx = builder.build()

expect(ptx).to_contain(".local .s64 local_buf[8];")
```

</details>

### PTX Builder - Thread IDs

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates thread ID access for x dimension

- generates thread ID access for x dimension


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates thread ID access for x dimension")
var builder = PtxBuilder__create((8, 6))
builder.emit_get_thread_id("%tid_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %tid_x, %tid.x;")
```

</details>

#### generates thread ID access for y dimension

- generates thread ID access for y dimension


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates thread ID access for y dimension")
var builder = PtxBuilder__create((8, 6))
builder.emit_get_thread_id("%tid_y", 1)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %tid_y, %tid.y;")
```

</details>

#### generates block ID access

- generates block ID access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates block ID access")
var builder = PtxBuilder__create((8, 6))
builder.emit_get_block_id("%bid_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %bid_x, %ctaid.x;")
```

</details>

#### generates block dim access

- generates block dim access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates block dim access")
var builder = PtxBuilder__create((8, 6))
builder.emit_get_block_dim("%bdim_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %bdim_x, %ntid.x;")
```

</details>

#### generates grid dim access

- generates grid dim access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates grid dim access")
var builder = PtxBuilder__create((8, 6))
builder.emit_get_grid_dim("%gdim_x", 0)
val ptx = builder.build()

expect(ptx).to_contain("mov.u32 %gdim_x, %nctaid.x;")
```

</details>

#### computes global thread ID

- computes global thread ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes global thread ID")
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

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates block-level barrier

- generates block-level barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates block-level barrier")
var builder = PtxBuilder__create((8, 6))
builder.emit_barrier()
val ptx = builder.build()

expect(ptx).to_contain("bar.sync 0;")
```

</details>

#### generates CTA memory barrier

- generates CTA memory barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates CTA memory barrier")
var builder = PtxBuilder__create((8, 6))
builder.emit_membar_cta()
val ptx = builder.build()

expect(ptx).to_contain("membar.cta;")
```

</details>

#### generates global memory barrier

- generates global memory barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates global memory barrier")
var builder = PtxBuilder__create((8, 6))
builder.emit_membar_gl()
val ptx = builder.build()

expect(ptx).to_contain("membar.gl;")
```

</details>

#### generates system memory barrier

- generates system memory barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates system memory barrier")
var builder = PtxBuilder__create((8, 6))
builder.emit_membar_sys()
val ptx = builder.build()

expect(ptx).to_contain("membar.sys;")
```

</details>

### PTX Builder - Atomic Operations

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates atomic add

- generates atomic add


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates atomic add")
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_add("%r0", PrimitiveType.I64, "%addr", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.add.u64 %r0, [%addr], %val;")
```

</details>

#### generates atomic min

- generates atomic min


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates atomic min")
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_min("%r0", PrimitiveType.I32, "%addr", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.min.s32 %r0, [%addr], %val;")
```

</details>

#### generates atomic max

- generates atomic max


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates atomic max")
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_max("%r0", PrimitiveType.U64, "%addr", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.max.u64 %r0, [%addr], %val;")
```

</details>

#### generates atomic compare-and-swap

- generates atomic compare-and-swap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates atomic compare-and-swap")
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_cas("%r0", PrimitiveType.I64, "%addr", "%cmp", "%val", MemorySpace.Global)
val ptx = builder.build()

expect(ptx).to_contain("atom.global.cas.b64 %r0, [%addr], %cmp, %val;")
```

</details>

#### generates shared memory atomic add

- generates shared memory atomic add


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates shared memory atomic add")
var builder = PtxBuilder__create((8, 6))
builder.emit_atomic_add("%r0", PrimitiveType.I32, "%saddr", "%val", MemorySpace.Shared)
val ptx = builder.build()

expect(ptx).to_contain("atom.shared.add.s32 %r0, [%saddr], %val;")
```

</details>

### PTX Builder - Type Conversions

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### converts int to float

- converts int to float


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts int to float")
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%f0", PrimitiveType.F32, "%r0", PrimitiveType.I32)
val ptx = builder.build()

expect(ptx).to_contain("cvt.rn.f32.s32 %f0, %r0;")
```

</details>

#### converts float to int

- converts float to int


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts float to int")
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%r0", PrimitiveType.I64, "%f0", PrimitiveType.F64)
val ptx = builder.build()

expect(ptx).to_contain("cvt.rzi.s64.f64 %r0, %f0;")
```

</details>

#### converts float to float

- converts float to float


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts float to float")
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%f0", PrimitiveType.F64, "%f1", PrimitiveType.F32)
val ptx = builder.build()

expect(ptx).to_contain("cvt.rn.f64.f32 %f0, %f1;")
```

</details>

#### converts int to int

- converts int to int


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("converts int to int")
var builder = PtxBuilder__create((8, 6))
builder.emit_convert("%r0", PrimitiveType.I64, "%r1", PrimitiveType.I32)
val ptx = builder.build()

expect(ptx).to_contain("cvt.s64.s32 %r0, %r1;")
```

</details>

### PTX Builder - Math Intrinsics

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates sin approximation

- generates sin approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates sin approximation")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_sin("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("sin.approx.f32 %f0, %f1;")
```

</details>

#### generates cos approximation

- generates cos approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates cos approximation")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_cos("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("cos.approx.f32 %f0, %f1;")
```

</details>

#### generates sqrt approximation

- generates sqrt approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates sqrt approximation")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_sqrt("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("sqrt.approx.f32 %f0, %f1;")
```

</details>

#### generates abs

- generates abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates abs")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_abs("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("abs.f32 %f0, %f1;")
```

</details>

#### generates fused multiply-add

- generates fused multiply-add


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates fused multiply-add")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_fma("%f0", PrimitiveType.F32, "%f1", "%f2", "%f3")
val ptx = builder.build()

expect(ptx).to_contain("fma.rn.f32 %f0, %f1, %f2, %f3;")
```

</details>

#### generates exp2 approximation

- generates exp2 approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates exp2 approximation")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_ex2("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("ex2.approx.f32 %f0, %f1;")
```

</details>

#### generates log2 approximation

- generates log2 approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates log2 approximation")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_lg2("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("lg2.approx.f32 %f0, %f1;")
```

</details>

#### generates reciprocal approximation

- generates reciprocal approximation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates reciprocal approximation")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_rcp("%f0", PrimitiveType.F32, "%f1")
val ptx = builder.build()

expect(ptx).to_contain("rcp.approx.f32 %f0, %f1;")
```

</details>

#### generates min instruction

- generates min instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates min instruction")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_min("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("min.f32 %f0, %f1, %f2;")
```

</details>

#### generates max instruction

- generates max instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates max instruction")
var builder = PtxBuilder__create((8, 6))
builder.emit_intrinsic_max("%f0", PrimitiveType.F32, "%f1", "%f2")
val ptx = builder.build()

expect(ptx).to_contain("max.f32 %f0, %f1, %f2;")
```

</details>

### PTX Builder - Control Flow

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates unconditional branch

- generates unconditional branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates unconditional branch")
var builder = PtxBuilder__create((8, 6))
builder.emit_branch("BB1")
val ptx = builder.build()

expect(ptx).to_contain("bra BB1;")
```

</details>

#### generates conditional branch

- generates conditional branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates conditional branch")
var builder = PtxBuilder__create((8, 6))
builder.emit_branch_if("%p0", "BB_true")
val ptx = builder.build()

expect(ptx).to_contain("@%p0 bra BB_true;")
```

</details>

#### generates negated conditional branch

- generates negated conditional branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates negated conditional branch")
var builder = PtxBuilder__create((8, 6))
builder.emit_branch_if_not("%p0", "BB_false")
val ptx = builder.build()

expect(ptx).to_contain("@!%p0 bra BB_false;")
```

</details>

#### generates labels

- generates labels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates labels")
var builder = PtxBuilder__create((8, 6))
builder.emit_label("BB0")
builder.emit_line("nop;")
val ptx = builder.build()

expect(ptx).to_contain("BB0:")
```

</details>

#### generates return instruction

- generates return instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates return instruction")
var builder = PtxBuilder__create((8, 6))
builder.emit_ret()
val ptx = builder.build()

expect(ptx).to_contain("ret;")
```

</details>

#### generates exit instruction

- generates exit instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates exit instruction")
var builder = PtxBuilder__create((8, 6))
builder.emit_exit()
val ptx = builder.build()

expect(ptx).to_contain("exit;")
```

</details>

### PTX Builder - Function Calls

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### generates function call with return value

- generates function call with return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates function call with return value")
var builder = PtxBuilder__create((8, 6))
builder.emit_call("%r0", PrimitiveType.I64, "device_func", ["%r1", "%r2"], [PrimitiveType.I64, PrimitiveType.I64])
val ptx = builder.build()

expect(ptx).to_contain("call (__call_0_retval), device_func, (__call_0_arg_0, __call_0_arg_1);")
```

</details>

#### generates void function call

- generates void function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates void function call")
var builder = PtxBuilder__create((8, 6))
builder.emit_call_void("void_func", ["%r0"], [PrimitiveType.I64])
val ptx = builder.build()

expect(ptx).to_contain("call void_func, (__call_0_arg_0);")
```

</details>

### CUDA Type Mapper - Primitive Types

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### maps integer types to PTX

- maps integer types to PTX
   - Expected: mapper.ptx_type(PrimitiveType.I64) equals `.s64`
   - Expected: mapper.ptx_type(PrimitiveType.I32) equals `.s32`
   - Expected: mapper.ptx_type(PrimitiveType.I16) equals `.s16`
   - Expected: mapper.ptx_type(PrimitiveType.I8) equals `.s8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps integer types to PTX")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.I64)).to_equal(".s64")
expect(mapper.ptx_type(PrimitiveType.I32)).to_equal(".s32")
expect(mapper.ptx_type(PrimitiveType.I16)).to_equal(".s16")
expect(mapper.ptx_type(PrimitiveType.I8)).to_equal(".s8")
```

</details>

#### maps unsigned integer types to PTX

- maps unsigned integer types to PTX
   - Expected: mapper.ptx_type(PrimitiveType.U64) equals `.u64`
   - Expected: mapper.ptx_type(PrimitiveType.U32) equals `.u32`
   - Expected: mapper.ptx_type(PrimitiveType.U16) equals `.u16`
   - Expected: mapper.ptx_type(PrimitiveType.U8) equals `.u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps unsigned integer types to PTX")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.U64)).to_equal(".u64")
expect(mapper.ptx_type(PrimitiveType.U32)).to_equal(".u32")
expect(mapper.ptx_type(PrimitiveType.U16)).to_equal(".u16")
expect(mapper.ptx_type(PrimitiveType.U8)).to_equal(".u8")
```

</details>

#### maps float types to PTX

- maps float types to PTX
   - Expected: mapper.ptx_type(PrimitiveType.F64) equals `.f64`
   - Expected: mapper.ptx_type(PrimitiveType.F32) equals `.f32`
   - Expected: mapper.ptx_type(PrimitiveType.F16) equals `.f16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps float types to PTX")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.F64)).to_equal(".f64")
expect(mapper.ptx_type(PrimitiveType.F32)).to_equal(".f32")
expect(mapper.ptx_type(PrimitiveType.F16)).to_equal(".f16")
```

</details>

#### maps bool to predicate

- maps bool to predicate
   - Expected: mapper.ptx_type(PrimitiveType.Bool) equals `.pred`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps bool to predicate")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_type(PrimitiveType.Bool)).to_equal(".pred")
```

</details>

### CUDA Type Mapper - Compute Capabilities

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### detects half precision support

- detects half precision support
   - Expected: mapper_old.supports_half_precision() is false
   - Expected: mapper_new.supports_half_precision() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects half precision support")
val mapper_old = CudaTypeMapper__create_sm(5, 0)
val mapper_new = CudaTypeMapper__create_sm(7, 0)
expect(mapper_old.supports_half_precision()).to_equal(false)
expect(mapper_new.supports_half_precision()).to_equal(true)
```

</details>

#### detects tensor core support

- detects tensor core support
   - Expected: mapper_old.supports_tensor_cores() is false
   - Expected: mapper_new.supports_tensor_cores() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects tensor core support")
val mapper_old = CudaTypeMapper__create_sm(6, 1)
val mapper_new = CudaTypeMapper__create_sm(7, 0)
expect(mapper_old.supports_tensor_cores()).to_equal(false)
expect(mapper_new.supports_tensor_cores()).to_equal(true)
```

</details>

#### reports correct max threads per block

- reports correct max threads per block
   - Expected: mapper.max_threads_per_block() equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports correct max threads per block")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.max_threads_per_block()).to_equal(1024)
```

</details>

#### reports correct warp size

- reports correct warp size
   - Expected: mapper.warp_size() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports correct warp size")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.warp_size()).to_equal(32)
```

</details>

#### reports correct shared memory for Ampere

- reports correct shared memory for Ampere
   - Expected: mapper.max_shared_memory() equals `163840`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports correct shared memory for Ampere")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.max_shared_memory()).to_equal(163840)
```

</details>

#### reports correct shared memory for Volta

- reports correct shared memory for Volta
   - Expected: shared_mem equals `96 * 1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports correct shared memory for Volta")
val mapper = CudaTypeMapper__create_sm(7, 0)
val shared_mem = mapper.max_shared_memory()
expect(shared_mem).to_equal(96 * 1024)
```

</details>

### CUDA Type Mapper - Memory Spaces

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### maps global memory space

- maps global memory space
   - Expected: mapper.ptx_state_space(MemorySpace.Global) equals `.global`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps global memory space")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Global)).to_equal(".global")
```

</details>

#### maps shared memory space

- maps shared memory space
   - Expected: mapper.ptx_state_space(MemorySpace.Shared) equals `.shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps shared memory space")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Shared)).to_equal(".shared")
```

</details>

#### maps local memory space

- maps local memory space
   - Expected: mapper.ptx_state_space(MemorySpace.Local) equals `.local`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps local memory space")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Local)).to_equal(".local")
```

</details>

#### maps constant memory space

- maps constant memory space
   - Expected: mapper.ptx_state_space(MemorySpace.Constant) equals `.const`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps constant memory space")
val mapper = CudaTypeMapper__create_sm(8, 6)
expect(mapper.ptx_state_space(MemorySpace.Constant)).to_equal(".const")
```

</details>

### Launch Configuration

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### creates 1D launch config

- creates 1D launch config
   - Expected: config.grid_x equals `4`
   - Expected: config.grid_y equals `1`
   - Expected: config.grid_z equals `1`
   - Expected: config.block_x equals `256`
   - Expected: config.total_threads() equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates 1D launch config")
val config = LaunchConfig.for_1d(1024, 256)
expect(config.grid_x).to_equal(4)
expect(config.grid_y).to_equal(1)
expect(config.grid_z).to_equal(1)
expect(config.block_x).to_equal(256)
expect(config.total_threads()).to_equal(1024)
```

</details>

#### rounds up grid size for non-divisible total

- rounds up grid size for non-divisible total
   - Expected: config.grid_x equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rounds up grid size for non-divisible total")
val config = LaunchConfig.for_1d(1000, 256)
expect(config.grid_x).to_equal(4)
expect(config.total_threads()).to_be_greater_than(999)
```

</details>

#### creates 2D launch config

- creates 2D launch config
   - Expected: config.grid_x equals `32`
   - Expected: config.grid_y equals `32`
   - Expected: config.block_x equals `16`
   - Expected: config.block_y equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates 2D launch config")
val config = LaunchConfig.for_2d(512, 512, 16, 16)
expect(config.grid_x).to_equal(32)
expect(config.grid_y).to_equal(32)
expect(config.block_x).to_equal(16)
expect(config.block_y).to_equal(16)
```

</details>

#### computes total blocks

- computes total blocks
   - Expected: config.total_blocks() equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes total blocks")
val config = LaunchConfig.for_2d(512, 512, 16, 16)
expect(config.total_blocks()).to_equal(1024)
```

</details>

#### computes threads per block

- computes threads per block
   - Expected: config.threads_per_block() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes threads per block")
val config = LaunchConfig.for_2d(512, 512, 16, 16)
expect(config.threads_per_block()).to_equal(256)
```

</details>

#### validates valid config

- validates valid config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates valid config")
val config = LaunchConfig.for_1d(1024, 256)
val err = config.validate()
expect(err).to_be_nil()
```

</details>

#### rejects zero block size

- rejects zero block size
   - Expected: config.block_x equals `0`
   - Expected: err ?? "" equals `Block dimensions must be positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects zero block size")
val config = LaunchConfig.for_1d(1024, 0)
expect(config.block_x).to_equal(0)
val err = config.validate()
expect(err).to_not_be_nil()
expect(err ?? "").to_equal("Block dimensions must be positive")
```

</details>

#### adds shared memory to config

- adds shared memory to config
   - Expected: config.shared_mem_bytes equals `4096`
   - Expected: config.block_x equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds shared memory to config")
val config = LaunchConfig.for_1d(1024, 256).with_shared_mem(4096)
expect(config.shared_mem_bytes).to_equal(4096)
expect(config.block_x).to_equal(256)
```

</details>

### PTX Builder - Constants

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### loads integer constant

- loads integer constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads integer constant")
var builder = PtxBuilder__create((8, 6))
builder.emit_const_int("%r0", PrimitiveType.I64, 42)
val ptx = builder.build()

expect(ptx).to_contain("mov.s64 %r0, 42;")
```

</details>

#### loads unsigned integer constant

- loads unsigned integer constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads unsigned integer constant")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c0aced857aee76db85a0031a70606a77e9bb4b16b773eed51921f5fcf83de08`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c0aced857aee76db85a0031a70606a77e9bb4b16b773eed51921f5fcf83de08`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c0aced857aee76db85a0031a70606a77e9bb4b16b773eed51921f5fcf83de08`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/gpu_ptx_gen_spec.spl
mirror: doc/06_spec/03_system/feature/usage/gpu_ptx_gen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/gpu_ptx_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/gpu_ptx_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/gpu_ptx_gen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/gpu_ptx_gen_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: CUDA not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gpu_ptx_gen_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates correct PTX header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gpu_ptx_gen_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates correct target for Volta' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
