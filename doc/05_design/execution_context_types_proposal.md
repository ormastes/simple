# Execution Context Types - Design Proposal

**Feature**: Compile-time tracking of execution location (CPU, GPU, specific devices)
**Inspiration**: Similar to how `Future<T>` tracks async computation
**Date**: 2026-01-10 (Updated: 2026-01-12)
**Syntax**: Uses `<>` for generic/template types (updated from `[]`)

---

## Executive Summary

Add type-level tracking of where code executes using generic types like `Host<id, T>` and `Gpu<device, T>`, mirroring how `Promise<T>` tracks async computation.

**Key Benefits**:
- ✅ Compile-time verification of device affinity
- ✅ Automatic scheduling based on type
- ✅ Memory transfer optimization (no host↔device copies)
- ✅ Type-safe heterogeneous computing

---

## Current State Analysis

### How Future/Promise Works (Model to Follow)

#### 1. Type Level
```rust
// In src/type/src/lib.rs
Type::Generic {
    name: "Promise",
    args: vec![Type::TypeParam("T")],
}
```

#### 2. Effect Level
```rust
// In src/type/src/effects.rs
pub enum Effect {
    Async,  // Function returns Promise<T>
    Sync,   // Function returns T directly
}
```

#### 3. Runtime Level
```rust
// In src/runtime/src/value/async_gen.rs
pub struct RuntimeFuture {
    pub header: HeapHeader,
    pub state: u64,           // Pending/ready
    pub result: RuntimeValue, // Result value
    pub body_func: u64,       // Resume function
    pub async_state: u64,     // State machine state
}
```

### Current Device Handling

#### GPU Backend Selection
```rust
// In src/runtime/src/value/gpu_backend.rs
pub enum GpuBackendType {
    Cpu,      // Software emulation
    Vulkan,   // Cross-platform GPU
    Cuda,     // NVIDIA GPU
}
```

#### Device Abstraction
```rust
// In src/gpu/src/device.rs
pub struct Device {
    pub id: u32,
    pub name: String,
    pub backend: GpuBackend,
}
```

**Gap**: Devices tracked at runtime only, not in type system!

---

## Proposed Design

### Option 1: Generic Type Approach (Recommended)

Add execution context as **generic type parameters**:

```simple
# Type constructors
type HostComputation<HostId, T>
type GpuComputation<DeviceId, T>
type DeviceComputation<Device, T>  # General device

# Examples
let cpu_task: HostComputation<0, Int> = compute_on_cpu()
let gpu_task: GpuComputation<0, [f32]> = compute_on_gpu()
```

**Advantages**:
- ✅ Reuses existing generic type infrastructure
- ✅ Type checker validates device compatibility
- ✅ Composable with other types (e.g., `Promise<GpuComputation<0, T>>`)
- ✅ Clear separation: type = where, value = what

### Option 2: Effect-Based Approach

Add execution context as **effect annotations**:

```simple
@gpu(device: 0)
fn matmul(a: Tensor, b: Tensor) -> Tensor:
    # Guaranteed to run on GPU 0
    ...

@host(cpu: 2)
fn preprocess(data: List) -> Tensor:
    # Guaranteed to run on CPU 2
    ...
```

**Advantages**:
- ✅ Familiar annotation syntax
- ✅ Effect inference can propagate device requirements
- ✅ Simpler syntax for common cases

**Disadvantages**:
- ⚠️ Effects are function-level, not value-level
- ⚠️ Can't track device in intermediate values

### Option 3: Hybrid Approach (Most Powerful)

Combine both type and effect tracking:

```simple
# Effect annotation for function contract
@gpu(device: 0)
fn train_model(data: Tensor) -> GpuComputation<0, Model>:
    # Type guarantees result is on GPU 0
    # Effect guarantees function executes on GPU 0
    ...

# Type system tracks device through pipeline
let data: HostComputation<_, Tensor> = load_data()
let gpu_data: GpuComputation<0, Tensor> = data.to_device(0)
let result: GpuComputation<0, f32> = gpu_matmul(gpu_data, gpu_data)
let cpu_result: HostComputation<_, f32> = result.to_host()
```

**Advantages**:
- ✅ Type-level tracking for values
- ✅ Effect-level tracking for functions
- ✅ Compiler enforces device data flow
- ✅ Automatic transfer minimization

---

## Detailed Design: Hybrid Approach

### 1. Type System Extensions

#### Add Device Type
```rust
// In src/type/src/lib.rs
pub enum Type {
    // Existing variants...

    // New: Execution context types
    HostComputation {
        host_id: Box<Type>,  // Type-level host ID (literal or symbolic)
        result: Box<Type>,   // Result type
    },
    GpuComputation {
        device_id: Box<Type>, // Type-level device ID
        result: Box<Type>,    // Result type
    },
    DeviceComputation {
        device: Box<Type>,    // Device enum/value
        result: Box<Type>,    // Result type
    },
}
```

#### Device Literals
```rust
// Device ID as type-level literal
Type::DeviceLiteral {
    kind: DeviceKind,  // Host, Gpu, Accelerator
    id: u32,           // Device index
}

pub enum DeviceKind {
    Host,       // CPU
    Gpu,        // GPU
    Accelerator,// TPU, IPU, etc.
}
```

### 2. Effect System Extensions

```rust
// In src/type/src/effects.rs
pub enum Effect {
    // Existing
    Async,
    Sync,
    Pure,

    // New execution context effects
    HostExec(HostId),         // Execute on specific CPU
    GpuExec(DeviceId),        // Execute on specific GPU
    DeviceExec(DeviceSpec),   // Execute on specified device
    AnyDevice,                // Can run on any device
}

pub struct HostId {
    pub cpu: u32,              // CPU core/socket ID
    pub numa_node: Option<u32>,// NUMA node if applicable
}

pub struct DeviceId {
    pub device: u32,           // Device index
    pub backend: GpuBackendType,
}

pub enum DeviceSpec {
    Host(HostId),
    Gpu(DeviceId),
    Auto,                      // Runtime chooses
}
```

### 3. Runtime Representation

```rust
// In src/runtime/src/value/device_computation.rs
#[repr(C)]
pub struct RuntimeDeviceComputation {
    pub header: HeapHeader,
    pub device_spec: ExecutionContext,
    pub state: u64,            // Pending/ready
    pub result: RuntimeValue,  // Result when ready
    pub kernel_func: u64,      // Function to execute
    pub ctx: RuntimeValue,     // Captured context
}

pub enum ExecutionContext {
    Host {
        cpu_id: u32,
        numa_node: Option<u32>,
    },
    Gpu {
        device_id: u32,
        backend: GpuBackendType,
        stream: Option<u64>,   // CUDA stream for async
    },
    Auto,  // Let scheduler decide
}
```

### 4. Language Syntax

#### Type Annotations
```simple
# Explicit device types
let x: Host<0, Int> = 42
let y: Gpu<0, Tensor> = allocate_tensor([1024, 1024])

# Enum-based device specification
enum Device:
    CPU(id: Int)
    GPU(id: Int, backend: GpuBackend)
    TPU(id: Int)

let z: DeviceComputation<Device.GPU(0, Cuda), [f32]> = ...
```

#### Effect Annotations
```simple
# Function-level device specification
@gpu(device=0)
fn matmul(a: Tensor, b: Tensor) -> Tensor:
    # Runs on GPU 0
    ...

@host(cpu=2, numa=0)
fn parallel_reduce(data: List) -> f64:
    # Runs on CPU 2, NUMA node 0
    ...

@device(auto)
fn generic_compute(x: Int) -> Int:
    # Scheduler chooses device
    x * 2
```

#### Device Transfer Operators
```simple
# Explicit transfers
let host_data: Host<_, Tensor> = load_data()
let gpu_data: Gpu<0, Tensor> = host_data.to_gpu(0)
let result: Gpu<0, f32> = gpu_matmul(gpu_data, gpu_data)
let cpu_result: Host<_, f32> = result.to_host()

# Implicit transfers (compiler inserts)
fn mixed_compute(x: Host<_, Int>) -> Gpu<0, Int>:
    # Compiler inserts transfer
    x + 1  # Implicitly transferred to GPU 0
```

### 5. Type Inference Rules

#### Device Inference
```
Γ ⊢ e : Host<h, T>    Γ ⊢ f : T → U
─────────────────────────────────────────
Γ ⊢ f(e) : Host<h, U>  (if f is @host)


Γ ⊢ e : Gpu<d, T>     Γ ⊢ f : T → U
─────────────────────────────────────────
Γ ⊢ f(e) : Gpu<d, U>   (if f is @gpu(d))


Γ ⊢ e1 : Host<h, T>   Γ ⊢ e2 : Gpu<d, T>
─────────────────────────────────────────────
ERROR: Device mismatch (without transfer)
```

#### Transfer Inference
```
Γ ⊢ e : Host<h1, T>   target = Gpu<d, _>
──────────────────────────────────────────
Γ ⊢ e.to_gpu(d) : Gpu<d, T>


Γ ⊢ e : Gpu<d, T>     target = Host<h, _>
──────────────────────────────────────────
Γ ⊢ e.to_host() : Host<h, T>
```

#### Auto Transfer Insertion
```simple
# User writes:
@gpu(0)
fn compute(x: Int) -> Int:
    let data = load_from_disk()  # Returns Host<_, Int>
    data + 1                      # ERROR: device mismatch

# Compiler suggests:
@gpu(0)
fn compute(x: Int) -> Int:
    let data = load_from_disk()       # Host<_, Int>
    let gpu_data = data.to_gpu(0)     # Gpu<0, Int> (auto-inserted)
    gpu_data + 1                       # Gpu<0, Int>
```

---

## Implementation Plan

### Phase 1: Type System Foundation

**Files to modify**:
- `src/type/src/lib.rs` - Add `DeviceComputation` type variants
- `src/type/src/effects.rs` - Add device execution effects
- `src/parser/src/ast/nodes/effects.rs` - Parse `@gpu`, `@host` annotations

**Tasks**:
1. Define `Type::HostComputation`, `Type::GpuComputation`
2. Add `Effect::HostExec`, `Effect::GpuExec`
3. Implement type equality for device types
4. Add device ID literals to type system

### Phase 2: Effect Inference

**Files to modify**:
- `src/type/src/effects.rs` - Extend effect inference
- `src/type/src/checker.rs` - Integrate device inference

**Tasks**:
1. Infer device effects from `@gpu`, `@host` annotations
2. Propagate device requirements through call chains
3. Detect device mismatches
4. Suggest transfer points

### Phase 3: Runtime Support

**Files to create/modify**:
- `src/runtime/src/value/device_computation.rs` (new)
- `src/runtime/src/executor.rs` - Device-aware scheduling
- `src/runtime/src/value/heap.rs` - Add heap object type

**Tasks**:
1. Implement `RuntimeDeviceComputation` struct
2. Add device scheduling to executor
3. Integrate with GPU backend selection
4. Add device transfer primitives

### Phase 4: Memory Management

**Files to modify**:
- `src/runtime/src/memory/gc.rs` - Device-aware GC
- `src/gpu/src/memory.rs` - GPU memory allocation

**Tasks**:
1. Track device memory separately
2. Implement device→host finalizers
3. Add unified memory support (optional)
4. Handle cross-device references

### Phase 5: Optimization

**Files to modify**:
- `src/compiler/src/codegen/` - Device-aware codegen
- `src/type/src/checker.rs` - Transfer minimization

**Tasks**:
1. Minimize host↔device transfers
2. Pipeline multiple GPU ops
3. Batch transfers
4. Use asynchronous transfers

---

## Example Use Cases

### Use Case 1: Neural Network Training

```simple
enum Device:
    CPU(id: Int)
    GPU(id: Int)

class Model:
    weights: Gpu<0, Tensor>

    @gpu(device=0)
    fn forward(self, input: Gpu<0, Tensor>) -> Gpu<0, Tensor>:
        # All computation stays on GPU 0
        let h1 = self.weights.matmul(input)
        let h2 = relu(h1)
        h2

    @gpu(device=0)
    fn backward(self, grad: Gpu<0, Tensor>) -> Gpu<0, Tensor>:
        # Gradient computation on GPU 0
        ...

# Training loop
fn train(model: Model, data: Host<_, Tensor>) -> Model:
    # Transfer once
    let gpu_data: Gpu<0, Tensor> = data.to_gpu(0)

    for epoch in range(100):
        # All ops stay on GPU
        let output: Gpu<0, Tensor> = model.forward(gpu_data)
        let loss: Gpu<0, f32> = compute_loss(output, targets)
        let grads: Gpu<0, Tensor> = model.backward(loss)

        # Update weights (GPU→GPU, no transfer)
        model.weights = model.weights - 0.01 * grads

    model
```

### Use Case 2: Multi-GPU Pipeline

```simple
@gpu(device=0)
fn preprocess(data: Gpu<0, Tensor>) -> Gpu<0, Tensor>:
    # Preprocessing on GPU 0
    normalize(data)

@gpu(device=1)
fn inference(model: Gpu<1, Model>, data: Gpu<1, Tensor>) -> Gpu<1, Tensor>:
    # Inference on GPU 1
    model.forward(data)

@gpu(device=2)
fn postprocess(output: Gpu<2, Tensor>) -> Gpu<2, Tensor>:
    # Postprocessing on GPU 2
    apply_nms(output)

# Pipeline
fn process(data: Host<_, Tensor>) -> Host<_, Tensor>:
    let d0: Gpu<0, Tensor> = data.to_gpu(0)
    let preprocessed: Gpu<0, Tensor> = preprocess(d0)

    # Transfer GPU 0 → GPU 1
    let d1: Gpu<1, Tensor> = preprocessed.to_gpu(1)
    let result: Gpu<1, Tensor> = inference(model, d1)

    # Transfer GPU 1 → GPU 2
    let d2: Gpu<2, Tensor> = result.to_gpu(2)
    let final: Gpu<2, Tensor> = postprocess(d2)

    # Transfer GPU 2 → Host
    final.to_host()
```

### Use Case 3: CPU Affinity

```simple
@host(cpu=0, numa=0)
fn worker_0(data: Host<0, List>) -> Host<0, f64>:
    # Runs on CPU 0, NUMA node 0
    # Data locality guaranteed
    data.sum()

@host(cpu=1, numa=0)
fn worker_1(data: Host<1, List>) -> Host<1, f64>:
    # Runs on CPU 1, same NUMA node
    data.mean()

fn parallel_compute(data: List) -> (f64, f64):
    # Split work across CPUs
    let chunk0: Host<0, List> = data.slice(0, n/2)
    let chunk1: Host<1, List> = data.slice(n/2, n)

    # Parallel execution with CPU affinity
    let sum: Host<0, f64> = worker_0(chunk0)
    let mean: Host<1, f64> = worker_1(chunk1)

    (sum.to_any(), mean.to_any())  # Merge to Any device
```

---

## Comparison with Other Languages

| Feature | Simple (Proposed) | Rust | Julia | Dex | Futhark |
|---------|------------------|------|-------|-----|---------|
| Device tracking | Type-level | Manual | Runtime | Type-level | Type-level |
| Transfer checking | Compile-time | Runtime | Runtime | Compile-time | Compile-time |
| Multi-device | ✅ | Manual | ✅ | ❌ | ❌ |
| CPU affinity | ✅ | Manual | ❌ | ❌ | ❌ |
| Effect inference | ✅ | ❌ | ❌ | ✅ | ❌ |

---

## Open Questions

1. **Device ID Representation**: Literal integers vs symbolic names vs enum?
   - **Recommendation**: Support all three, unify at type level

2. **Async + Device**: How do `Promise<Gpu<0, T>>` and `Gpu<0, Promise<T>>` differ?
   - **Recommendation**: `Promise<Gpu<0, T>>` = async computation that produces GPU value

3. **Memory Model**: Unified memory vs explicit transfers?
   - **Recommendation**: Start with explicit, add unified as optimization

4. **Error Handling**: What if device doesn't exist?
   - **Recommendation**: Compile-time error if known, runtime error if dynamic

5. **Type Inference**: Infer device from context or require explicit annotations?
   - **Recommendation**: Infer when unambiguous, require annotation at boundaries

---

## Next Steps

1. **Prototype Phase 1**: Add basic type system support
   - Define `Type::DeviceComputation` variants
   - Parse `@gpu`, `@host` annotations
   - Implement type checking rules

2. **Validation**: Test with tensor dimension inference
   - Combine `Gpu<0, TensorShape<[batch:1..64, 784]>>`
   - Verify shape + device tracking works together

3. **Runtime Proof-of-Concept**: Single GPU support
   - Implement `RuntimeGpuComputation`
   - Add `.to_gpu()`, `.to_host()` transfers
   - Test with simple matmul

4. **Documentation**: Write user guide
   - How to annotate functions
   - When transfers occur
   - Performance best practices

5. **Community Feedback**: Share proposal
   - Gather use cases
   - Refine syntax
   - Validate approach

---

## Conclusion

**Recommendation**: Implement **Hybrid Approach** (Option 3)

**Why**:
- ✅ Maximum expressiveness (type + effect tracking)
- ✅ Leverages existing infrastructure (generic types, effect system)
- ✅ Natural extension of Future/Promise model
- ✅ Enables powerful optimizations (transfer minimization, pipelining)
- ✅ Type safety prevents device mismatches

**Estimated Effort**:
- Phase 1 (Type system): 2-3 weeks
- Phase 2 (Effect inference): 2 weeks
- Phase 3 (Runtime): 3-4 weeks
- Phase 4 (Memory): 2 weeks
- Phase 5 (Optimization): 3-4 weeks
- **Total**: 12-15 weeks for full implementation

**Starting Point**: Begin with Phase 1 prototype to validate approach.

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
**Status**: Design Proposal (Ready for Review)
