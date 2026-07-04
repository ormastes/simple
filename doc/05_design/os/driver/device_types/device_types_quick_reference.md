# Execution Context Types - Quick Reference

**TL;DR**: Add `Host<id, T>` and `Gpu<device, T>` types like `Promise<T>` for async.

---

## Syntax Summary

### Type Annotations

```simple
# Basic device types
let x: Host<0, Int> = 42                    # On CPU 0
let y: Gpu<0, Tensor> = allocate([1024])    # On GPU 0

# With device enum
enum Device:
    CPU(id: Int)
    GPU(id: Int, backend: String)

let z: DeviceComputation<Device.GPU(0, "cuda"), [f32]> = ...

# Anonymous device (scheduler chooses)
let w: Host<_, Int> = compute()             # Any CPU
let v: Gpu<_, Tensor> = train()             # Any GPU
```

### Function Annotations

```simple
# GPU function
@gpu(device=0)
fn matmul(a: Tensor, b: Tensor) -> Tensor:
    # Guaranteed to run on GPU 0
    a @ b

# CPU function with affinity
@host(cpu=2, numa=0)
fn reduce(data: List) -> f64:
    # Runs on CPU 2, NUMA node 0
    data.sum()

# Device-agnostic (can run anywhere)
@device(auto)
fn add(x: Int, y: Int) -> Int:
    x + y
```

### Device Transfers

```simple
# Explicit transfers
let host_data: Host<_, Tensor> = load_data()
let gpu_data: Gpu<0, Tensor> = host_data.to_gpu(0)
let result: Gpu<0, Tensor> = matmul(gpu_data, gpu_data)
let final: Host<_, Tensor> = result.to_host()

# Compiler-inserted transfers
@gpu(0)
fn process(data: Host<_, Int>) -> Gpu<0, Int>:
    data + 1  # Compiler inserts: data.to_gpu(0) + 1
```

---

## Complete Examples

### Example 1: Simple GPU Computation

```simple
# Load PyTorch-style tensor library
import ml.torch.{Tensor, zeros, randn}

# Create tensors on different devices
let cpu_tensor: Host<_, Tensor> = randn([1024, 1024])
let gpu_tensor: Gpu<0, Tensor> = cpu_tensor.to_gpu(0)

# GPU computation (stays on GPU)
@gpu(device=0)
fn compute(a: Gpu<0, Tensor>, b: Gpu<0, Tensor>) -> Gpu<0, Tensor>:
    let c = a.matmul(b)
    let d = c + a
    d

let result: Gpu<0, Tensor> = compute(gpu_tensor, gpu_tensor)

# Transfer back to CPU for saving
let cpu_result: Host<_, Tensor> = result.to_host()
save_to_disk(cpu_result, "output.pt")
```

### Example 2: Multi-GPU Training Pipeline

```simple
# Data parallel training across 4 GPUs
enum GpuId:
    GPU0 | GPU1 | GPU2 | GPU3

class Model:
    weights: Gpu<0, Tensor>  # Master copy on GPU 0

    # Replicate model to specific GPU
    fn replicate(self, device: Int) -> Gpu<device, Model>:
        Model(weights: self.weights.to_gpu(device))

# Training step on specific GPU
@gpu(device)
fn train_step<device>(
    model: Gpu<device, Model>,
    data: Gpu<device, Tensor>,
    labels: Gpu<device, Tensor>
) -> Gpu<device, Tensor>:
    let output = model.forward(data)
    let loss = cross_entropy(output, labels)
    let grads = backward(loss)
    grads

# Main training loop
fn train_data_parallel(model: Model, dataset: List[Tensor]):
    # Split data across GPUs
    let batches = dataset.chunk(4)

    # Replicate model to each GPU
    let model0: Gpu<0, Model> = model
    let model1: Gpu<1, Model> = model.replicate(1)
    let model2: Gpu<2, Model> = model.replicate(2)
    let model3: Gpu<3, Model> = model.replicate(3)

    for epoch in range(100):
        # Transfer data to GPUs
        let data0: Gpu<0, Tensor> = batches[0].to_gpu(0)
        let data1: Gpu<1, Tensor> = batches[1].to_gpu(1)
        let data2: Gpu<2, Tensor> = batches[2].to_gpu(2)
        let data3: Gpu<3, Tensor> = batches[3].to_gpu(3)

        # Parallel computation (all GPUs in parallel)
        let grads0: Gpu<0, Tensor> = train_step(model0, data0, labels0)
        let grads1: Gpu<1, Tensor> = train_step(model1, data1, labels1)
        let grads2: Gpu<2, Tensor> = train_step(model2, data2, labels2)
        let grads3: Gpu<3, Tensor> = train_step(model3, data3, labels3)

        # Gather gradients to GPU 0
        let all_grads = [
            grads0,
            grads1.to_gpu(0),
            grads2.to_gpu(0),
            grads3.to_gpu(0),
        ]

        # Average and update
        let avg_grad: Gpu<0, Tensor> = average(all_grads)
        model0.weights = model0.weights - 0.01 * avg_grad

        # Broadcast updated weights
        model1.weights = model0.weights.to_gpu(1)
        model2.weights = model0.weights.to_gpu(2)
        model3.weights = model0.weights.to_gpu(3)
```

### Example 3: CPU Affinity for NUMA

```simple
# Bind computation to specific NUMA nodes
struct NumaNode:
    id: Int
    cpus: List[Int]

@host(numa=0)
fn worker_node0(data: Host<0, List[f64]>) -> Host<0, f64>:
    # All allocations on NUMA node 0
    # All computation on CPUs of node 0
    data.iter().sum()

@host(numa=1)
fn worker_node1(data: Host<1, List[f64]>) -> Host<1, f64>:
    # All allocations on NUMA node 1
    # All computation on CPUs of node 1
    data.iter().mean()

fn numa_aware_compute(data: List[f64]) -> (f64, f64):
    let n = data.len() / 2

    # Pin data to specific NUMA nodes
    let chunk0: Host<0, List[f64]> = data.slice(0, n).pin_numa(0)
    let chunk1: Host<1, List[f64]> = data.slice(n, data.len()).pin_numa(1)

    # Parallel execution with NUMA affinity
    let sum: Host<0, f64> = worker_node0(chunk0)
    let mean: Host<1, f64> = worker_node1(chunk1)

    # Results can be merged (move to Any device)
    (sum.unpin(), mean.unpin())
```

### Example 4: Heterogeneous Pipeline

```simple
# Different stages on different devices
@host(cpu=0)
fn load_data() -> Host<0, Image>:
    read_from_disk("data.jpg")

@gpu(device=0)
fn preprocess(img: Gpu<0, Image>) -> Gpu<0, Tensor>:
    img.resize([224, 224]).normalize()

@gpu(device=1)  # Different GPU for inference
fn inference(model: Gpu<1, Model>, data: Gpu<1, Tensor>) -> Gpu<1, Tensor>:
    model.forward(data)

@host(cpu=0)
fn postprocess(result: Host<0, Tensor>) -> Host<0, String>:
    let class_id = result.argmax()
    get_class_name(class_id)

# Full pipeline
fn classify_image() -> String:
    let img: Host<0, Image> = load_data()

    # CPU → GPU 0
    let gpu_img: Gpu<0, Image> = img.to_gpu(0)
    let preprocessed: Gpu<0, Tensor> = preprocess(gpu_img)

    # GPU 0 → GPU 1
    let gpu1_data: Gpu<1, Tensor> = preprocessed.to_gpu(1)
    let result: Gpu<1, Tensor> = inference(model, gpu1_data)

    # GPU 1 → CPU
    let cpu_result: Host<0, Tensor> = result.to_host()
    postprocess(cpu_result)
```

---

## Type System Rules

### Device Type Compatibility

```simple
# Same device, same type → OK
let x: Gpu<0, Int> = 42
let y: Gpu<0, Int> = x  # OK

# Different device → ERROR
let z: Gpu<1, Int> = x  # ERROR: device mismatch

# Need explicit transfer
let z: Gpu<1, Int> = x.to_gpu(1)  # OK
```

### Function Type Signatures

```simple
# Input and output on same device
@gpu(0)
fn square(x: Gpu<0, Int>) -> Gpu<0, Int>:
    x * x

# Input on one device, output on another (requires transfer)
@gpu(1)
fn move_and_compute(x: Gpu<0, Int>) -> Gpu<1, Int>:
    x.to_gpu(1) * 2

# Generic over device
fn generic_square<D>(x: DeviceComputation<D, Int>) -> DeviceComputation<D, Int>:
    x * x
```

### Inference Rules

```simple
# Compiler infers device from context
@gpu(0)
fn train():
    let data = load_data()  # Inferred as Host<_, Tensor>
    let gpu_data = data.to_gpu(0)  # Explicit: Gpu<0, Tensor>

    let x = gpu_data + 1  # Inferred: Gpu<0, Tensor> (stays on GPU)
    let y = x * 2          # Inferred: Gpu<0, Tensor> (stays on GPU)
    let z = y.relu()       # Inferred: Gpu<0, Tensor> (stays on GPU)

    z  # Returns: Gpu<0, Tensor>
```

---

## Runtime Behavior

### Memory Layout

```rust
// GPU computation object (heap-allocated)
#[repr(C)]
struct RuntimeGpuComputation {
    header: HeapHeader,
    device_id: u32,           // Target device
    state: u64,               // Pending/ready
    result: RuntimeValue,     // Result value
    device_ptr: u64,          // Device memory pointer
}

// Host computation object
#[repr(C)]
struct RuntimeHostComputation {
    header: HeapHeader,
    cpu_id: u32,              // Target CPU
    numa_node: Option<u32>,   // NUMA affinity
    result: RuntimeValue,     // Result value
}
```

### Transfer Operations

```simple
# .to_gpu(device) compiles to:
# 1. Allocate device memory
# 2. Copy host → device (cudaMemcpy or equivalent)
# 3. Return GPU computation object

# .to_host() compiles to:
# 1. Allocate host memory
# 2. Copy device → host
# 3. Free device memory (or defer to GC)
# 4. Return host computation object
```

### Scheduling

```rust
// Executor checks device context
match computation.execution_context {
    ExecutionContext::Host { cpu_id, numa_node } => {
        // Pin thread to CPU
        set_cpu_affinity(cpu_id);
        if let Some(node) = numa_node {
            bind_numa_node(node);
        }
        execute_on_cpu(computation);
    }
    ExecutionContext::Gpu { device_id, backend } => {
        // Set CUDA device context
        set_current_device(device_id, backend);
        execute_on_gpu(computation);
    }
    ExecutionContext::Auto => {
        // Let scheduler choose best device
        schedule_auto(computation);
    }
}
```

---

## Integration with Tensor Dimensions

Combine device types with tensor dimension tracking:

```simple
import verification.models.tensor_dimensions.{Dim, TensorShape}

# Tensor with both shape and device tracking
type TypedGpuTensor = Gpu<0, TensorShape<[batch:1..64, features:784]>>

@gpu(device=0)
fn matmul_typed(
    input: Gpu<0, TensorShape<[batch:1..64, in:784]>>,
    weight: Gpu<0, TensorShape<[in:784, out:256]>>
) -> Gpu<0, TensorShape<[batch:1..64, out:256]>>:
    # Both shape AND device verified at compile time!
    infer_matmul_shape(input, weight)

# Usage
let input: Gpu<0, TensorShape<[batch:32, 784]>> = load_batch().to_gpu(0)
let weight: Gpu<0, TensorShape<[784, 256]>> = model.weight

# Type system verifies:
# ✅ Shapes compatible (784 matches)
# ✅ Devices match (both GPU 0)
# ✅ Output shape correct ([32, 256])
let output = matmul_typed(input, weight)
```

---

## Error Messages

```simple
# Device mismatch error
let x: Gpu<0, Int> = 42
let y: Gpu<1, Int> = x
# ERROR: Device mismatch
#   Expected: Gpu<1, Int>
#   Found:    Gpu<0, Int>
#
# Help: Use .to_gpu(1) to transfer to GPU 1
#   let y: Gpu<1, Int> = x.to_gpu(1)

# Missing device annotation
fn compute(x: Tensor) -> Tensor:
    x.matmul(x)  # Uses GPU internally
# ERROR: Function uses GPU but has no @gpu annotation
#
# Help: Add device annotation:
#   @gpu(device=0)
#   fn compute(x: Gpu<0, Tensor>) -> Gpu<0, Tensor>:
```

---

## Performance Considerations

### Transfer Minimization

```simple
# BAD: Multiple transfers
@gpu(0)
fn bad(x: Gpu<0, Int>) -> Gpu<0, Int>:
    let h1 = x.to_host()     # GPU → CPU (slow!)
    let h2 = h1 + 1
    let g1 = h2.to_gpu(0)    # CPU → GPU (slow!)
    g1

# GOOD: Stay on device
@gpu(0)
fn good(x: Gpu<0, Int>) -> Gpu<0, Int>:
    x + 1  # All on GPU (fast!)
```

### Async Transfers

```simple
# Overlap computation and transfer
@gpu(0) async
fn async_pipeline(data: List[Gpu<0, Tensor>]) -> Gpu<0, Tensor>:
    let results = []

    for batch in data:
        # Start transfer while previous batch computes
        let next_batch: Promise<Gpu<0, Tensor>> =
            batch.to_gpu_async(0)

        # Compute current batch
        let result = compute(current_batch)
        results.push(result)

        # Await transfer
        current_batch = await next_batch

    concat(results)
```

---

## Summary

**Key Points**:
1. ✅ Device tracking at type level (`Host<id, T>`, `Gpu<device, T>`)
2. ✅ Effect annotations for functions (`@gpu`, `@host`)
3. ✅ Explicit transfers (`.to_gpu()`, `.to_host()`)
4. ✅ Compiler verification of device compatibility
5. ✅ Integration with tensor dimension tracking
6. ✅ Multi-device and NUMA support

**Next**: See full design in `execution_context_types_proposal.md`

---

**Prepared by**: Claude Code Assistant
**Date**: 2026-01-10
