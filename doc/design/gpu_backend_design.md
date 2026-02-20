# GPU Backend Design Document

This document describes the architecture and design of GPU compute support in the Simple compiler.

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Type System Extensions](#type-system-extensions)
4. [MIR GPU Instructions](#mir-gpu-instructions)
5. [Code Generation Pipeline](#code-generation-pipeline)
6. [CUDA Backend](#cuda-backend)
7. [Vulkan Backend](#vulkan-backend)
8. [Runtime Integration](#runtime-integration)
9. [Future Extensions](#future-extensions)

---

## Overview

### Goals

1. **Unified API**: Single programming model for CUDA and Vulkan
2. **Type Safety**: Compile-time verification of GPU operations
3. **Performance**: Minimal overhead, direct hardware access
4. **Extensibility**: Easy to add new GPU backends

### Non-Goals

1. Graphics rendering (focus is compute)
2. Automatic parallelization
3. GPU memory management (explicit allocation)

### Design Principles

- **Explicit over implicit**: Users control device selection, memory allocation
- **Backend-agnostic**: High-level API hides backend differences
- **Fail-fast**: Invalid operations fail at compile time when possible
- **Zero-cost abstractions**: Wrapper types compile away

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      Simple Source Code                          │
│   kernel fn add(a: [f32]_gpu, b: [f32]_gpu, c: [f32]_gpu)       │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                         Lexer/Parser                             │
│   - kernel keyword                                               │
│   - shared declarations                                          │
│   - <<<>>> launch syntax                                         │
│   - GPU intrinsics                                               │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                            HIR                                   │
│   - DeviceType: CPU, GPU, CUDA(id), Vulkan(id)                  │
│   - MemorySpace: Global, Shared, Local, Constant, Uniform       │
│   - Function.is_kernel flag                                      │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                            MIR                                   │
│   - GpuKernelDef, GpuLaunch                                     │
│   - GpuGlobalId, GpuLocalId, GpuBlockId, ...                    │
│   - GpuBarrier, GpuMemFence                                     │
│   - GpuAtomicOp, GpuSharedAlloc                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
              ┌───────────────┴───────────────┐
              ▼                               ▼
┌─────────────────────────┐     ┌─────────────────────────┐
│     CUDA Backend        │     │    Vulkan Backend       │
│   ┌─────────────────┐   │     │   ┌─────────────────┐   │
│   │ CudaTypeMapper  │   │     │   │VulkanTypeMapper │   │
│   └─────────────────┘   │     │   └─────────────────┘   │
│   ┌─────────────────┐   │     │   ┌─────────────────┐   │
│   │   PtxBuilder    │   │     │   │  SpirvBuilder   │   │
│   └─────────────────┘   │     │   └─────────────────┘   │
│   ┌─────────────────┐   │     │   ┌─────────────────┐   │
│   │  CudaBackend    │   │     │   │ VulkanBackend   │   │
│   └─────────────────┘   │     │   └─────────────────┘   │
└─────────────────────────┘     └─────────────────────────┘
              │                               │
              ▼                               ▼
        ┌──────────┐                   ┌──────────┐
        │   PTX    │                   │  SPIR-V  │
        └──────────┘                   └──────────┘
              │                               │
              ▼                               ▼
┌─────────────────────────┐     ┌─────────────────────────┐
│    CUDA Runtime FFI     │     │   Vulkan Runtime FFI    │
│   (io.cuda_ffi)         │     │   (io.vulkan_ffi)       │
└─────────────────────────┘     └─────────────────────────┘
```

---

## Type System Extensions

### DeviceType Enum

Location: `src/compiler/hir_types.spl:507`

```simple
enum DeviceType:
    CPU                # Host CPU
    GPU                # Generic GPU (auto-select)
    CUDA(id: i64)      # Specific CUDA device
    Vulkan(id: i64)    # Specific Vulkan device
```

**Usage:**
- Type annotations: `[f32]_gpu`, `Tensor<f32, [N, M], GPU>`
- Runtime dispatch based on device type
- Validation that GPU operations target GPU memory

### MemorySpace Enum

Location: `src/compiler/hir_types.spl:515`

```simple
enum MemorySpace:
    Global      # Device global memory (slow, large)
    Shared      # Workgroup shared memory (fast, small)
    Local       # Thread-local memory (registers/stack)
    Constant    # Read-only constant memory
    Uniform     # Vulkan uniform buffer
```

**Memory Hierarchy:**

```
┌─────────────────────────────────────────┐
│              Global Memory              │  Slow, GBs
│         (Device DRAM)                   │
└─────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────┐
│           Constant Memory               │  Cached, read-only
│        (Shared across blocks)           │
└─────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────┐
│            Shared Memory                │  Fast, KBs per block
│         (Per block/workgroup)           │
└─────────────────────────────────────────┘
              │
              ▼
┌─────────────────────────────────────────┐
│            Local Memory                 │  Registers, per thread
│           (Per thread)                  │
└─────────────────────────────────────────┘
```

### PrimitiveType Extensions

Location: `src/compiler/backend/common/type_mapper.spl`

Added unsigned types and half-precision:
- `U64`, `U32`, `U16`, `U8` - Unsigned integers
- `F16` - Half-precision float (GPU compute)

---

## MIR GPU Instructions

Location: `src/compiler/mir_data.spl`

### Kernel Definition

```simple
GpuKernelDef(name: text, params: [MirLocal], body_block: BlockId)
```

Defines a GPU kernel function. Kernel functions:
- Cannot return values (void return)
- Cannot call non-kernel functions
- Have access to thread/block IDs
- Can use shared memory

### Kernel Launch

```simple
GpuLaunch(kernel: MirOperand, grid_dim: MirOperand, block_dim: MirOperand, args: [MirOperand])
```

Launches a kernel on the GPU. Parameters:
- `kernel`: Reference to kernel function
- `grid_dim`: Number of blocks (x, y, z)
- `block_dim`: Threads per block (x, y, z)
- `args`: Kernel arguments (device pointers)

### Thread ID Instructions

```simple
GpuGlobalId(dest: LocalId, dim: i64)   # Global thread index
GpuLocalId(dest: LocalId, dim: i64)    # Local thread index within block
GpuBlockId(dest: LocalId, dim: i64)    # Block index
GpuBlockDim(dest: LocalId, dim: i64)   # Block dimensions
GpuGridDim(dest: LocalId, dim: i64)    # Grid dimensions
```

Dimension `dim` is 0, 1, or 2 for x, y, z.

### Synchronization Instructions

```simple
GpuBarrier(scope: GpuBarrierScope)     # Thread barrier
GpuMemFence(scope: GpuMemoryScope)     # Memory fence
```

Barrier scopes:
- `Block`: All threads in block
- `Subgroup`: Threads in warp/subgroup

Memory scopes:
- `Device`: All threads on device
- `Workgroup`: Threads in workgroup
- `Subgroup`: Threads in subgroup

### Memory Instructions

```simple
GpuSharedAlloc(dest: LocalId, type_: MirType, size: i64)
```

Allocates shared memory visible to all threads in a block.

### Atomic Instructions

```simple
GpuAtomicOp(dest: LocalId, op: GpuAtomicOpKind, ptr: MirOperand, value: MirOperand)
```

Atomic operations:
- `Add`, `Sub`, `Min`, `Max`
- `And`, `Or`, `Xor`
- `Exchange`, `CompareExchange`

---

## Code Generation Pipeline

### Phase 1: Parsing

1. **Lexer** recognizes:
   - `kernel` keyword → `TokenKind.KwKernel`
   - `shared` keyword → `TokenKind.KwShared`
   - `<<<` and `>>>` → Launch syntax tokens

2. **Parser** produces:
   - `Function` with `is_kernel = true`
   - `StmtKind.SharedVal/SharedVar` for shared memory
   - `ExprKind.KernelLaunch` for launch expressions
   - `ExprKind.GpuIntrinsic` for GPU built-ins

### Phase 2: HIR Lowering

1. Kernel functions get special treatment:
   - No implicit `self` parameter
   - Return type must be void
   - Cannot capture closures

2. GPU intrinsics are validated:
   - Argument count checking
   - Context checking (must be in kernel)

### Phase 3: MIR Generation

1. Kernel bodies become `GpuKernelDef`
2. Launch expressions become `GpuLaunch`
3. Intrinsics become corresponding MIR instructions

### Phase 4: Backend Code Generation

1. **Type Mapping**: Map Simple types to target types
2. **Instruction Selection**: Map MIR to target instructions
3. **Register Allocation**: Assign registers/locals
4. **Code Emission**: Generate PTX or SPIR-V

---

## CUDA Backend

### CudaTypeMapper

Location: `src/compiler/backend/cuda_type_mapper.spl`

Maps Simple types to CUDA/PTX types:

| Simple | CUDA | PTX |
|--------|------|-----|
| `i64` | `long long` | `.s64` |
| `i32` | `int` | `.s32` |
| `f64` | `double` | `.f64` |
| `f32` | `float` | `.f32` |
| `f16` | `half` | `.f16` |
| `bool` | `bool` | `.pred` |
| `[T]_gpu` | `T*` | `.u64` (pointer) |

Memory space mapping:
- `Global` → `__global__`
- `Shared` → `__shared__`
- `Constant` → `__constant__`
- `Local` → (default)

### PtxBuilder

Location: `src/compiler/backend/cuda/ptx_builder.spl`

Generates PTX assembly:

```ptx
.version 7.0
.target sm_50
.address_size 64

.visible .entry kernel_name(
    .param .u64 param0,
    .param .u64 param1
) {
    .reg .pred p;
    .reg .b32 tid;

    mov.u32 tid, %tid.x;
    // ... kernel body ...
    ret;
}
```

Key features:
- Module header generation
- Entry point declaration
- Register allocation
- Special register access (`%tid.x`, `%ctaid.x`, etc.)
- Memory operations with address spaces
- Barrier and atomic instructions

### CudaBackend

Location: `src/compiler/backend/cuda_backend.spl`

Orchestrates CUDA code generation:

1. Create type mapper
2. Create PTX builder
3. For each kernel:
   - Emit kernel prologue
   - Generate instructions
   - Emit kernel epilogue
4. Produce final PTX module

---

## Vulkan Backend

### VulkanTypeMapper

Location: `src/compiler/backend/vulkan_type_mapper.spl`

Maps Simple types to SPIR-V types:

| Simple | SPIR-V |
|--------|--------|
| `i64` | `OpTypeInt 64 1` |
| `i32` | `OpTypeInt 32 1` |
| `u32` | `OpTypeInt 32 0` |
| `f64` | `OpTypeFloat 64` |
| `f32` | `OpTypeFloat 32` |
| `bool` | `OpTypeBool` |

Memory space (storage class) mapping:
- `Global` → `StorageBuffer`
- `Shared` → `Workgroup`
- `Uniform` → `Uniform`
- `Local` → `Function`

### SpirvBuilder

Location: `src/compiler/backend/vulkan/spirv_builder.spl`

Generates SPIR-V assembly:

```spirv
; SPIR-V
; Version: 1.3
; Generator: Simple Compiler
OpCapability Shader
OpMemoryModel Logical GLSL450
OpEntryPoint GLCompute %main "main" %gl_GlobalInvocationID
OpExecutionMode %main LocalSize 256 1 1

; Decorations
OpDecorate %gl_GlobalInvocationID BuiltIn GlobalInvocationID
OpDecorate %buffer DescriptorSet 0
OpDecorate %buffer Binding 0

; Types
%void = OpTypeVoid
%int = OpTypeInt 32 1
%float = OpTypeFloat 32

; Entry point
%main = OpFunction %void None %void_func
%entry = OpLabel
; ... kernel body ...
OpReturn
OpFunctionEnd
```

Key features:
- Module header with capabilities
- Entry point declaration
- Descriptor set layout
- Built-in variable declarations
- Compute shader boilerplate

### VulkanBackend

Location: `src/compiler/backend/vulkan_backend.spl`

Orchestrates Vulkan code generation:

1. Create type mapper
2. Create SPIR-V builder
3. Emit module header
4. For each kernel:
   - Declare entry point
   - Set up descriptors
   - Generate instructions
5. Produce final SPIR-V module

---

## Runtime Integration

### SFFI Architecture

Two-tier pattern for FFI bindings:

```simple
# Tier 1: Raw extern declaration
extern fn rt_cuda_malloc(size: i64) -> i64

# Tier 2: Type-safe wrapper
fn cuda_alloc(size: i64) -> CudaPtr:
    val ptr = rt_cuda_malloc(size)
    CudaPtr(ptr: ptr, size: size, is_valid: ptr != 0)
```

### CUDA FFI

Location: `src/app/io/cuda_ffi.spl`

Categories:
- Device management: `rt_cuda_device_count`, `rt_cuda_set_device`
- Memory: `rt_cuda_malloc`, `rt_cuda_free`, `rt_cuda_memcpy_*`
- Kernels: `rt_cuda_compile_ptx`, `rt_cuda_launch_kernel`
- Sync: `rt_cuda_synchronize`, `rt_cuda_stream_*`

### Vulkan FFI

Location: `src/app/io/vulkan_ffi.spl`

Categories:
- Instance/device: `rt_vulkan_init`, `rt_vulkan_select_device`
- Buffers: `rt_vulkan_alloc_buffer`, `rt_vulkan_copy_*`
- Shaders: `rt_vulkan_compile_spirv`, `rt_vulkan_compile_glsl`
- Pipelines: `rt_vulkan_create_compute_pipeline`
- Execution: `rt_vulkan_dispatch`, `rt_vulkan_submit_and_wait`

### Standard Library

Location: `src/lib/gpu/`

Unified high-level API:

```simple
use std.gpu.*

val gpu = gpu_default()
val buffer = gpu_alloc(gpu, 1024)
gpu_vector_add(gpu, a, b, c, n)
gpu.sync()
```

---

## Future Extensions

### Tensor Cores (NVIDIA)

Support for matrix multiply-accumulate:

```simple
# Future syntax
kernel fn gemm_tensor(A: Matrix<f16>, B: Matrix<f16>, C: Matrix<f32>):
    wmma_load_a(a_frag, A)
    wmma_load_b(b_frag, B)
    wmma_mma(c_frag, a_frag, b_frag, c_frag)
    wmma_store(C, c_frag)
```

### Ray Tracing

Vulkan ray tracing extensions:

```simple
# Future syntax
raytracing fn closest_hit(payload: RayPayload):
    payload.color = material.diffuse
```

### Cooperative Groups (CUDA)

Fine-grained thread synchronization:

```simple
# Future syntax
kernel fn cooperative_kernel():
    val tile = cooperative_tile(32)
    tile.sync()
    val sum = tile.reduce(value, add)
```

### Multi-GPU

Distributed execution across GPUs:

```simple
# Future syntax
val gpus = [gpu_cuda(0), gpu_cuda(1)]
parallel_for gpu in gpus:
    compute_shard(gpu, data.shard(gpu.id))
```

### Automatic Differentiation

GPU-accelerated autodiff:

```simple
# Future syntax
@differentiable
kernel fn loss_kernel(pred: [f32]_gpu, target: [f32]_gpu) -> f32:
    val idx = gpu_global_id(0)
    val diff = pred[idx] - target[idx]
    diff * diff
```

---

## File Locations

| Component | File |
|-----------|------|
| DeviceType, MemorySpace | `src/compiler/hir_types.spl` |
| GPU MIR instructions | `src/compiler/mir_data.spl` |
| TypeMapper trait | `src/compiler/backend/common/type_mapper.spl` |
| CudaTypeMapper | `src/compiler/backend/cuda_type_mapper.spl` |
| VulkanTypeMapper | `src/compiler/backend/vulkan_type_mapper.spl` |
| PtxBuilder | `src/compiler/backend/cuda/ptx_builder.spl` |
| SpirvBuilder | `src/compiler/backend/vulkan/spirv_builder.spl` |
| CudaBackend | `src/compiler/backend/cuda_backend.spl` |
| VulkanBackend | `src/compiler/backend/vulkan_backend.spl` |
| GPU intrinsics | `src/compiler/gpu_intrinsics.spl` |
| CUDA FFI | `src/app/io/cuda_ffi.spl` |
| Vulkan FFI | `src/app/io/vulkan_ffi.spl` |
| GPU stdlib | `src/lib/gpu/*.spl` |
| GPU test helpers | `src/lib/src/testing/gpu_helpers.spl` |
| GPU tests | `test/system/features/gpu/*.spl` |

---

## See Also

- [GPU Programming Guide](../guide/gpu_programming.md) - User guide
- [GPU API Reference](../api/gpu_api.md) - API documentation
- [Pipeline Operators Design](pipeline_operators_design.md) - Related: `~>` layer connect
