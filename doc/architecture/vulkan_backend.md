# Vulkan Backend Architecture

**Version:** 0.1.0
**Last Updated:** 2025-12-26

## Table of Contents

1. [Overview](#overview)
2. [Architecture Diagram](#architecture-diagram)
3. [Component Details](#component-details)
4. [Compilation Pipeline](#compilation-pipeline)
5. [Runtime Architecture](#runtime-architecture)
6. [SPIR-V Generation](#spir-v-generation)
7. [Memory Management](#memory-management)
8. [Performance Considerations](#performance-considerations)

## Overview

The Vulkan backend enables GPU compute in Simple by compiling MIR (Mid-level IR) to SPIR-V bytecode and executing it through the Vulkan API. The implementation spans three main layers:

1. **Compiler Layer**: MIR → SPIR-V translation
2. **Runtime Layer**: Vulkan device/buffer/kernel management
3. **FFI Layer**: C-compatible bridge between compiler and runtime

### Design Goals

- **Performance**: Minimal overhead, zero-copy where possible
- **Safety**: Type-safe API, automatic resource management
- **Portability**: Cross-platform (Windows, Linux, macOS)
- **Fallback**: Graceful degradation when GPU unavailable

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                     Simple Source Code                       │
│                      (GPU Kernel)                            │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                    Parser (AST)                              │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                   HIR (Type-checked)                         │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                   MIR (Mid-level IR)                         │
│              - 50+ instruction types                         │
│              - Effect annotations                            │
│              - Type information                              │
└────────────────────┬────────────────────────────────────────┘
                     │
            ┌────────┴────────┐
            │  Backend        │
            │  Selection      │
            └────────┬────────┘
                     │
         ┌───────────┴───────────┐
         │                       │
         ▼                       ▼
    ┌────────┐            ┌──────────┐
    │Vulkan  │            │Software  │
    │Backend │            │Fallback  │
    └───┬────┘            └──────────┘
        │
        ▼
┌─────────────────────────────────────────────────────────────┐
│                  SPIR-V Builder                              │
│  - Type mapping (TypeId → SPIR-V types)                     │
│  - Instruction lowering (MIR → SPIR-V ops)                  │
│  - Type-aware operations (OpIAdd vs OpFAdd)                 │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                  SPIR-V Bytecode                             │
│  - Valid Vulkan 1.1 SPIR-V                                  │
│  - Magic: 0x07230203                                        │
│  - Compute shader only                                      │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                  Runtime FFI Layer                           │
│  - 12 FFI functions (device, buffer, kernel)                │
│  - Handle-based API (u64 handles)                           │
│  - Error codes (i32 return values)                          │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                  Vulkan Runtime                              │
│  - Device management (VulkanDevice)                         │
│  - Buffer management (VulkanBuffer)                         │
│  - Pipeline compilation (ComputePipeline)                   │
│  - Kernel execution (dispatch)                              │
└────────────────────┬────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────┐
│                  Vulkan Driver                               │
│  - GPU vendor implementation                                │
│  - Hardware abstraction layer                               │
└─────────────────────────────────────────────────────────────┘
```

## Component Details

### 1. Backend Selection (`backend_trait.rs`)

**Purpose:** Choose appropriate backend for compilation.

**Key Types:**
```rust
pub enum BackendKind {
    Cranelift,      // CPU JIT
    Llvm,           // CPU AOT
    Vulkan,         // GPU (SPIR-V)
    Software,       // CPU fallback for GPU kernels
}
```

**Selection Logic:**
```rust
pub fn for_gpu_kernel(target: &Target) -> BackendKind {
    #[cfg(feature = "vulkan")]
    if VulkanBackend::supports_target(target) {
        return BackendKind::Vulkan;
    }

    BackendKind::Software  // Fallback
}
```

**Decision Points:**
- GPU kernels → `for_gpu_kernel()`
- Regular functions → `for_target()`
- Never mix: Vulkan/Software only for GPU, Cranelift/LLVM only for CPU

### 2. VulkanBackend (`vulkan/backend.rs`)

**Purpose:** Implement NativeBackend trait for SPIR-V generation.

**Structure:**
```rust
pub struct VulkanBackend {
    target: Target,
    validation_layers_enabled: bool,  // Debug only
}
```

**Key Methods:**
```rust
impl NativeBackend for VulkanBackend {
    fn compile(&mut self, module: &MirModule) -> Result<Vec<u8>>;
    fn name(&self) -> &'static str { "Vulkan SPIR-V" }
    fn supports_target(target: &Target) -> bool;
}
```

**Responsibilities:**
- Create SPIR-V module builder
- Compile MIR → SPIR-V
- Serialize to bytecode
- Return valid SPIR-V binary

### 3. SPIR-V Builder (`vulkan/spirv_builder.rs`)

**Purpose:** Translate MIR instructions to SPIR-V operations.

**Structure:**
```rust
pub struct SpirvModule {
    builder: rspirv::dr::Builder,
    vreg_types: HashMap<VReg, TypeId>,    // Track virtual register types
    // ... other state
}
```

**Key Operations:**
```rust
// Type mapping
fn type_id_to_spirv(&self, ty: TypeId) -> Result<Word>;

// Instruction lowering
fn lower_instruction(&mut self, instr: &Instruction) -> Result<()>;

// Type-aware operations
fn emit_binop(&mut self, op: BinOp, left: VReg, right: VReg, ty: TypeId) -> Result<VReg>;
```

**Type-Aware Lowering:**
```rust
match (op, type_id) {
    (BinOp::Add, TypeId::I32 | TypeId::I64) => builder.i_add(...),
    (BinOp::Add, TypeId::F32 | TypeId::F64) => builder.f_add(...),
    (BinOp::Div, TypeId::I32) => builder.s_div(...),  // Signed
    (BinOp::Div, TypeId::U32) => builder.u_div(...),  // Unsigned
    (BinOp::Div, TypeId::F32 | TypeId::F64) => builder.f_div(...),
    // ...
}
```

### 4. Runtime FFI (`runtime/value/gpu_vulkan.rs`)

**Purpose:** Expose Vulkan runtime to Simple via C-compatible functions.

**Handle Management:**
```rust
lazy_static! {
    static ref DEVICE_REGISTRY: Mutex<HashMap<u64, Arc<VulkanDevice>>>;
    static ref BUFFER_REGISTRY: Mutex<HashMap<u64, Arc<VulkanBuffer>>>;
    static ref PIPELINE_REGISTRY: Mutex<HashMap<u64, Arc<ComputePipeline>>>;
    static ref NEXT_HANDLE: AtomicU64 = AtomicU64::new(1);
}
```

**FFI Functions (12 total):**
```rust
// Device management
#[no_mangle] pub extern "C" fn rt_vk_available() -> i32;
#[no_mangle] pub extern "C" fn rt_vk_device_create() -> u64;
#[no_mangle] pub extern "C" fn rt_vk_device_free(handle: u64) -> i32;
#[no_mangle] pub extern "C" fn rt_vk_device_sync(handle: u64) -> i32;

// Buffer management
#[no_mangle] pub extern "C" fn rt_vk_buffer_alloc(device: u64, size: u64) -> u64;
#[no_mangle] pub extern "C" fn rt_vk_buffer_free(buffer: u64) -> i32;
#[no_mangle] pub extern "C" fn rt_vk_buffer_upload(buffer: u64, data: *const u8, size: u64) -> i32;
#[no_mangle] pub extern "C" fn rt_vk_buffer_download(buffer: u64, data: *mut u8, size: u64) -> i32;

// Kernel management
#[no_mangle] pub extern "C" fn rt_vk_kernel_compile(device: u64, spirv: *const u8, len: u64) -> u64;
#[no_mangle] pub extern "C" fn rt_vk_kernel_free(pipeline: u64) -> i32;
#[no_mangle] pub extern "C" fn rt_vk_kernel_launch(...) -> i32;
#[no_mangle] pub extern "C" fn rt_vk_kernel_launch_1d(...) -> i32;
```

**Error Handling:**
```rust
pub enum VulkanFfiError {
    Success = 0,
    NotAvailable = -1,
    InvalidHandle = -2,
    AllocationFailed = -3,
    CompilationFailed = -4,
    ExecutionFailed = -5,
    BufferTooSmall = -6,
    InvalidParameter = -7,
}
```

### 5. Vulkan Runtime (`runtime/vulkan/`)

**Purpose:** Manage Vulkan device, memory, and compute pipeline.

**Key Components:**

#### VulkanDevice
```rust
pub struct VulkanDevice {
    instance: Arc<VulkanInstance>,
    physical_device: vk::PhysicalDevice,
    device: ash::Device,
    compute_queue: vk::Queue,
    transfer_queue: vk::Queue,
    allocator: Arc<Mutex<gpu_allocator::vulkan::Allocator>>,
}
```

#### VulkanBuffer
```rust
pub struct VulkanBuffer {
    device: Arc<VulkanDevice>,
    buffer: vk::Buffer,
    allocation: VulkanAllocation,
    size: u64,
    usage: vk::BufferUsageFlags,
}
```

#### ComputePipeline
```rust
pub struct ComputePipeline {
    device: Arc<VulkanDevice>,
    shader_module: vk::ShaderModule,
    descriptor_set_layout: vk::DescriptorSetLayout,
    pipeline_layout: vk::PipelineLayout,
    pipeline: vk::Pipeline,
}
```

## Compilation Pipeline

### Phase 1: MIR Generation

Simple source → AST → HIR → MIR

**Key MIR Instructions for GPU:**
```rust
pub enum Instruction {
    // GPU intrinsics
    GpuGlobalId { dest: VReg, dim: u32 },
    GpuLocalId { dest: VReg, dim: u32 },
    GpuBarrier,
    GpuAtomicAdd { dest: VReg, addr: VReg, value: VReg },

    // Regular operations (type-aware in SPIR-V)
    BinOp { dest: VReg, op: BinOp, left: VReg, right: VReg, type_id: TypeId },
    Load { dest: VReg, addr: VReg, type_id: TypeId },
    Store { addr: VReg, value: VReg },

    // Control flow
    Branch { target: BlockId },
    CondBranch { cond: VReg, true_target: BlockId, false_target: BlockId },
    Return { value: Option<VReg> },
}
```

### Phase 2: Backend Selection

```rust
let backend_kind = BackendKind::for_gpu_kernel(&target);

match backend_kind {
    BackendKind::Vulkan => {
        let mut backend = VulkanBackend::new(target)?;
        let spirv = backend.compile(&mir_module)?;
        // ... runtime compilation
    }
    BackendKind::Software => {
        // CPU fallback via interpreter
    }
    _ => unreachable!("GPU kernels only use Vulkan or Software"),
}
```

### Phase 3: SPIR-V Generation

**Steps:**
1. Create SPIR-V module with capabilities and entry points
2. Declare types (map TypeId → SPIR-V types)
3. Compile functions:
   - Allocate SPIR-V registers for VRegs
   - Lower instructions to SPIR-V operations
   - Handle control flow (blocks, branches)
4. Serialize to bytecode

**Example Lowering:**

MIR:
```
BinOp { dest: v2, op: Add, left: v0, right: v1, type_id: F32 }
```

SPIR-V:
```
%2 = OpFAdd %float %0 %1
```

### Phase 4: Runtime Compilation

**Steps:**
1. Create Vulkan shader module from SPIR-V
2. Use spirv_reflect to extract descriptor set layouts
3. Create pipeline layout
4. Compile compute pipeline
5. Cache pipeline for reuse

## Runtime Architecture

### Device Lifecycle

```rust
// 1. Check availability
if rt_vk_available() == 0 { /* not available */ }

// 2. Create device
let device_handle = rt_vk_device_create();

// 3. Use device
// ...

// 4. Synchronize
rt_vk_device_sync(device_handle);

// 5. Free device
rt_vk_device_free(device_handle);
```

### Buffer Lifecycle

```rust
// 1. Allocate buffer
let buffer_handle = rt_vk_buffer_alloc(device_handle, size_bytes);

// 2. Upload data
rt_vk_buffer_upload(buffer_handle, data_ptr, size);

// 3. Use in kernel
// ...

// 4. Download results
rt_vk_buffer_download(buffer_handle, result_ptr, size);

// 5. Free buffer
rt_vk_buffer_free(buffer_handle);
```

### Kernel Execution

```rust
// 1. Compile kernel
let kernel_handle = rt_vk_kernel_compile(device_handle, spirv_ptr, spirv_len);

// 2. Launch kernel
let buffers = [buffer1, buffer2, buffer3];
rt_vk_kernel_launch_1d(
    kernel_handle,
    buffers.as_ptr(),
    buffers.len() as u64,
    global_size  // Total work items
);

// 3. Synchronize
rt_vk_device_sync(device_handle);

// 4. Free kernel
rt_vk_kernel_free(kernel_handle);
```

## SPIR-V Generation

### Type Mapping

| TypeId | SPIR-V Type | OpType |
|--------|-------------|--------|
| I32 | i32 | OpTypeInt 32 1 |
| I64 | i64 | OpTypeInt 64 1 |
| U32 | u32 | OpTypeInt 32 0 |
| U64 | u64 | OpTypeInt 64 0 |
| F32 | f32 | OpTypeFloat 32 |
| F64 | f64 | OpTypeFloat 64 |
| Bool | bool | OpTypeBool |

### Instruction Mapping

| MIR Instruction | SPIR-V Operation (i32) | SPIR-V Operation (f32) |
|-----------------|------------------------|------------------------|
| BinOp::Add | OpIAdd | OpFAdd |
| BinOp::Sub | OpISub | OpFSub |
| BinOp::Mul | OpIMul | OpFMul |
| BinOp::Div (signed) | OpSDiv | OpFDiv |
| BinOp::Div (unsigned) | OpUDiv | n/a |
| BinOp::Rem (signed) | OpSRem | OpFRem |
| BinOp::Rem (unsigned) | OpUMod | n/a |
| Comparison::Less | OpSLessThan / OpULessThan | OpFOrdLessThan |
| Comparison::LessEq | OpSLessThanEqual / OpULessThanEqual | OpFOrdLessThanEqual |
| Comparison::Greater | OpSGreaterThan / OpUGreaterThan | OpFOrdGreaterThan |
| Comparison::GreaterEq | OpSGreaterThanEqual / OpUGreaterThanEqual | OpFOrdGreaterThanEqual |
| Comparison::Equal | OpIEqual | OpFOrdEqual |
| Comparison::NotEqual | OpINotEqual | OpFOrdNotEqual |

### GPU Intrinsic Mapping

| MIR Intrinsic | SPIR-V Built-in |
|---------------|-----------------|
| GpuGlobalId(0) | gl_GlobalInvocationID.x |
| GpuGlobalId(1) | gl_GlobalInvocationID.y |
| GpuGlobalId(2) | gl_GlobalInvocationID.z |
| GpuLocalId(0) | gl_LocalInvocationID.x |
| GpuBarrier | OpControlBarrier |
| GpuAtomicAdd | OpAtomicIAdd |

### SPIR-V Module Structure

```
OpCapability Shader
OpMemoryModel Logical GLSL450
OpEntryPoint GLCompute %main "main"
OpExecutionMode %main LocalSize 256 1 1

; Types
%void = OpTypeVoid
%func = OpTypeFunction %void
%uint = OpTypeInt 32 0
%int = OpTypeInt 32 1
%float = OpTypeFloat 32

; Constants
%c_0 = OpConstant %uint 0
%c_1 = OpConstant %uint 1

; Main function
%main = OpFunction %void None %func
%entry = OpLabel
  ; ... instructions ...
  OpReturn
OpFunctionEnd
```

## Memory Management

### Device Memory

**Allocation Strategy:**
- Use `gpu-allocator` for memory management
- Allocate from device-local heap (fastest)
- Cache allocations for reuse (future optimization)

**Memory Types:**
```rust
// Device-local (fastest, not CPU-accessible)
vk::MemoryPropertyFlags::DEVICE_LOCAL

// Host-visible (CPU accessible, slower)
vk::MemoryPropertyFlags::HOST_VISIBLE | vk::MemoryPropertyFlags::HOST_COHERENT
```

### Buffer Transfers

**Upload (CPU → GPU):**
```rust
1. Create staging buffer (host-visible)
2. Map staging buffer to CPU memory
3. Copy data to staging buffer
4. Record copy command (vkCmdCopyBuffer)
5. Submit command buffer
6. Wait for completion
```

**Download (GPU → CPU):**
```rust
1. Create staging buffer (host-visible)
2. Record copy command (vkCmdCopyBuffer)
3. Submit command buffer
4. Wait for completion
5. Map staging buffer to CPU memory
6. Copy data from staging buffer
```

### Handle Management

**Design:**
- Handles are u64 values (0 = invalid)
- Atomic counter ensures unique handles
- HashMap stores handle → Arc<T> mappings
- Arc provides automatic cleanup when last reference dropped

**Thread Safety:**
- All registries protected by Mutex
- Locks held only during lookup/insert/remove
- No locks held during Vulkan operations (prevent deadlock)

## Performance Considerations

### Overhead Analysis

| Operation | Overhead | Dominant Factor |
|-----------|----------|-----------------|
| Backend creation | ~1ms | Vulkan device initialization |
| SPIR-V generation | ~10μs | MIR → SPIR-V translation |
| Kernel compilation | ~50ms | Vulkan pipeline compilation |
| Buffer allocation | ~100μs | GPU memory allocation |
| Buffer upload (1MB) | ~2ms | PCIe transfer (8 GB/s) |
| Kernel launch | ~50μs | Descriptor allocation + dispatch |
| Synchronization | varies | Depends on kernel execution time |

### Optimization Opportunities

**Implemented:**
- ✅ Zero-copy where possible (direct buffer mapping)
- ✅ Deterministic compilation (no random state)
- ✅ Feature-gated debug code (validation layers)

**Future:**
- ⏸️ Pipeline caching (avoid recompilation)
- ⏸️ Descriptor set caching (reduce allocation overhead)
- ⏸️ Async command submission (hide latency)
- ⏸️ Persistent staging buffers (reuse across transfers)
- ⏸️ Multi-device support (scale across GPUs)

### Bottlenecks

**Current:**
1. **Pipeline compilation** - 50ms per kernel
   - Solution: Cache compiled pipelines
2. **CPU↔GPU transfers** - Limited by PCIe bandwidth
   - Solution: Minimize transfers, batch operations
3. **Small datasets** - Overhead dominates for < 10K elements
   - Solution: Use CPU fallback for small data

## Testing Strategy

**Unit Tests (26 tests):**
- Backend selection logic
- SPIR-V generation
- Type mapping
- Determinism

**Integration Tests (11 tests):**
- End-to-end compilation
- Backend selection
- SPIR-V validation

**Test Coverage:** ~74% (37 of ~50 planned tests)

## References

- Vulkan Specification: https://www.vulkan.org/
- SPIR-V Specification: https://www.khronos.org/spir/
- rspirv Documentation: https://docs.rs/rspirv/
- ash (Vulkan bindings): https://docs.rs/ash/
- gpu-allocator: https://docs.rs/gpu-allocator/

## See Also

- [User Guide](../guides/vulkan_backend.md) - Using the Vulkan backend
- [Phase 4 Report](../report/VULKAN_PHASE4_COMPLETE_2025-12-26.md) - Implementation details
- [Phase 5 Report](../report/VULKAN_PHASE5_UNIT_TESTS_2025-12-26.md) - Test coverage
