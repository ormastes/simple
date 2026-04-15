# PyTorch Wrapper Design for Simple Language

**Date:** 2025-12-26
**Status:** Research Document
**Author:** Claude (Sonnet 4.5)

## Executive Summary

This document researches the design and implementation strategy for a PyTorch wrapper in the Simple programming language. Simple is a modern systems programming language with GPU capabilities, strong type safety, actor-based concurrency, and comprehensive FFI support. The goal is to provide seamless PyTorch integration leveraging Simple's unique features while maintaining performance and type safety.

**Recommended Approach:** Direct LibTorch (C++ API) FFI bindings with optional Python bridge for features not available in LibTorch.

---

## Table of Contents

1. [PyTorch Architecture](#1-pytorch-architecture)
2. [Python Interop Options](#2-python-interop-options)
3. [API Surface Design](#3-api-surface-design)
4. [Simple Language Integration](#4-simple-language-integration)
5. [Implementation Strategy](#5-implementation-strategy)
6. [Performance Considerations](#6-performance-considerations)
7. [Zero-Copy Data Sharing](#7-zero-copy-data-sharing)
8. [Recommended Architecture](#8-recommended-architecture)

---

## 1. PyTorch Architecture

### 1.1 LibTorch: The C++ Powerhouse

**Overview:** [LibTorch](https://docs.pytorch.org/cppdocs/) is the C++ distribution of PyTorch providing the same high-performance core that powers the Python API. As of 2025, LibTorch offers a [stable ABI](https://docs.pytorch.org/docs/stable/notes/libtorch_stable_abi.html) designed for production deployments.

**Key Components:**

1. **ATen (A Tensor Library)** - The foundational tensor and mathematical operation library
   - Core Tensor class with hundreds of operations
   - Device-agnostic design (CPU, CUDA, etc.)
   - Provides building blocks for all higher-level APIs
   - [Learn more about ATen](https://www.codegenes.net/blog/pytorch-aten-library/)

2. **Autograd Engine** - Automatic differentiation system
   - Records operations on tensors to form an autograd graph
   - Augments ATen Tensor class with gradient tracking
   - Enables backpropagation for training neural networks
   - [Python/C++ API documentation](https://docs.pytorch.org/cppdocs/)

3. **C++ Frontend** - High-level constructs for model building
   - `torch::nn::Module` base class for neural network modules
   - Optimizers (SGD, Adam, etc.)
   - Data loading utilities
   - Similar design philosophy to Python API
   - [C++ Frontend Guide](https://docs.pytorch.org/tutorials/advanced/cpp_frontend.html)

4. **TorchScript JIT** - Model optimization and deployment
   - **Deprecated as of 2025** - Use `torch.compile` instead
   - `torch.compile` uses graph compilation for optimization
   - Superior to TorchScript in handling arbitrary Python code
   - [torch.compile documentation](https://docs.pytorch.org/tutorials/intermediate/torch_compile_tutorial.html)

5. **Distributed Training** - `torch.distributed` package
   - Multiple parallelism strategies: DDP, FSDP2, TP, PP
   - DTensor and DeviceMesh abstractions
   - Support for NCCL, Gloo, MPI backends
   - [Distributed overview](https://docs.pytorch.org/tutorials/beginner/dist_overview.html)

### 1.2 CUDA/GPU Integration

**CUDA Semantics:**

- [CUDA memory management](https://docs.pytorch.org/docs/stable/notes/cuda.html) with caching allocator
- Memory transfer operations: `cpu()`, `cuda()`, `to(device)`
- CUDA streams for asynchronous execution
- [Memory profiling tools](https://docs.pytorch.org/docs/stable/torch_cuda_memory.html) with snapshot visualization
- Environment variable configuration: `PYTORCH_CUDA_ALLOC_CONF`
- GPUDirect Storage (CUDA 12.6+) for direct GPU-storage transfers

**2025 Updates:**

- CUDA 12.3 support with improved memory management
- Better Tensor Core utilization
- Enhanced debugging with memory snapshots at [pytorch.org/memory_viz](https://pytorch.org/memory_viz)

### 1.3 Memory Layout and Reference Counting

**Tensor Memory:**

- `torch.layout`: Dense (`torch.strided`) and sparse (`torch.sparse_coo`) layouts
- [Memory format](https://pytorch.org/blog/tensor-memory-format-matters/): Contiguous, ChannelsLast (NHWC), ChannelsLast3d (NTHWC)
- Each strided tensor has associated `torch.Storage` with strides
- Memory format determined by size and stride, not explicit attribute

**Reference Counting:**

- PyTorch C++ uses intrusive reference counting for tensors
- [`torch::Tensor::impl_`](https://github.com/pytorch/pytorch/issues/170137) weak reference counter for memory profiling
- Strict reference-count checks introduced in v2.3.1 for `torch.utils.swap_tensors`
- Important for integration with GC-based languages like Simple

---

## 2. Python Interop Options

### 2.1 CPython C API

**Official Resources:**

- [Extending Python with C/C++](https://docs.python.org/3/extending/extending.html)
- [Embedding Python in Applications](https://docs.python.org/3/extending/embedding.html)
- [Python/C API Reference Manual](https://docs.python.org/3/c-api/index.html)

**Key Capabilities:**

1. **Extending Python** - Write C/C++ extension modules
   - Custom types and functions callable from Python
   - Use `Python.h` header for API access
   - Compile to shared libraries (`.so`, `.pyd`)

2. **Embedding Python** - Run Python interpreter in C/C++ apps
   - `Py_Initialize()` to start interpreter
   - Execute Python code from C/C++
   - Access Python objects and call functions

**Considerations for Simple:**

- CPython C API is CPython-specific (doesn't work with PyPy, etc.)
- Requires managing Python GIL (Global Interpreter Lock)
- Need careful lifetime management between Python and Simple objects
- Manual reference counting with `Py_INCREF`/`Py_DECREF`

### 2.2 PyO3-Style Bindings (Rust Model)

**PyO3 Overview:**

- [PyO3](https://github.com/PyO3/pyo3) provides Rust ↔ Python bindings
- Two modes: Native Python modules in Rust, or embedding Python in Rust
- [Smart pointers](https://docs.rs/pyo3/latest/pyo3/): `Py<T>` and `Bound<'py, T>` with lifetime tracking
- [Design constraints](https://github.com/PyO3/PyO3/blob/main/guide/src/class.md): `#[pyclass]` types must have no lifetimes, no generics, thread-safe

**Lessons for Simple:**

1. **Lifetime Management** - Track Python object lifetimes with borrowed references
2. **Type Safety** - Use type system to prevent common errors (dangling refs, GIL violations)
3. **Build Integration** - Use [Maturin](https://maturin.rs) or similar for packaging
4. **Attribute Macros** - Declarative approach for exposing types/functions

### 2.3 PyTorch + Rust Integration Patterns

**tch-rs (Rust PyTorch Bindings):**

- [tch-rs](https://github.com/LaurentMazare/tch-rs) provides Rust bindings to LibTorch C++ API
- Direct bindings to LibTorch, no Python dependency
- [pyo3-tch](https://lib.rs/crates/pyo3-tch) bridges PyO3 and tch-rs
- Enables calling Rust/tch code from Python via PyO3

**Design Pattern (from [Transformer with PyTorch and Rust](https://jadon.io/blog/pytorch-rust/)):**

```rust
// Access Python PyTorch APIs from Rust when LibTorch lacks features
use pyo3::prelude::*;
use pyo3_tch::TensorExt; // Converts Python Tensor → Rust Tensor

#[pymodule]
fn my_module(py: Python, m: &PyModule) -> PyResult<()> {
    // Inject Python code to call PyTorch functions
    let torch_module = PyModule::from_code(
        py,
        "import torch\ndef scaled_attn(q,k,v): return torch.nn.functional.scaled_dot_product_attention(q,k,v)",
        "torch_helpers.py",
        "torch_helpers"
    )?;

    // Call Python function from Rust
    let result = torch_module
        .getattr("scaled_attn")?
        .call1((q_py, k_py, v_py))?
        .extract::<Tensor>()?; // Convert back to Rust

    Ok(())
}
```

**Applicability to Simple:**

- Simple has FFI capabilities for calling C/Rust functions
- Could use similar pattern: LibTorch for core operations, Python bridge for advanced features
- Zero-copy tensor conversion via DLPack (see section 7)

### 2.4 Julia's PyCall Pattern

**PyCall.jl:**

- [PyCall.jl](https://github.com/JuliaPy/PyCall.jl) enables Julia ↔ Python interop
- Shares large data structures without copying
- Uses [DLPack.jl](https://github.com/p-zubieta/DLPack.jl) for zero-copy tensor exchange
- Works with PyTorch, JAX, CuPy, etc.

**Zero-Copy Example:**

```julia
using PyCall, DLPack

torch = pyimport("torch")
py_tensor = torch.randn(100, 100)

# Zero-copy import via DLPack
jl_tensor = from_dlpack(py_tensor)

# Zero-copy export
py_tensor2 = DLPack.share(jl_tensor, torch.from_dlpack)
```

**Key Insight:** DLPack protocol enables zero-copy sharing across frameworks (see section 7).

---

## 3. API Surface Design

### 3.1 Tensor Creation and Operations

**Core Tensor API:**

```simple
# Tensor creation
let t1 = Tensor.zeros([3, 4], dtype: :f32, device: :cpu)
let t2 = Tensor.ones([3, 4], dtype: :f32, device: :cuda)
let t3 = Tensor.randn([3, 4], dtype: :f32)
let t4 = Tensor.from_array([[1.0, 2.0], [3.0, 4.0]])

# Operations (leverage Simple's operator overloading)
let sum = t1 + t2       # Element-wise addition
let prod = t1 * t2      # Element-wise multiplication
let matmul = t1 @ t2    # Matrix multiplication
let transposed = t1.transpose([1, 0])
let reshaped = t1.reshape([12])

# Reductions
let total = t1.sum()
let mean = t1.mean(dim: 0)
let max_val = t1.max()

# Device transfer
let cuda_tensor = t1.cuda()
let cpu_tensor = cuda_tensor.cpu()
let on_device = t1.to(device: :cuda, dtype: :f64)
```

**Design Principles:**

1. Follow Simple's type system and naming conventions
2. Use semantic types where appropriate (see section 4.1)
3. Leverage Simple's effect system for async operations
4. Provide both method syntax (`.sum()`) and function syntax (`Tensor.sum(t)`)

### 3.2 Autograd and Gradient Computation

**Gradient Tracking:**

```simple
# Enable gradient tracking
let x = Tensor.randn([3, 3], requires_grad: true)
let y = Tensor.randn([3, 3], requires_grad: true)

# Forward pass
let z = x @ y + x.sum()

# Backward pass
z.backward()

# Access gradients
let x_grad = x.grad
let y_grad = y.grad

# Gradient context managers
with torch.no_grad():
    let output = model(input)  # No gradient tracking

with torch.enable_grad():
    let output = model(input)  # Force gradient tracking
```

**Integration with Simple's Effect System:**

- Autograd operations are pure (no side effects)
- Gradient computation can be async for distributed training
- Use Simple's actor model for distributed gradient aggregation

### 3.3 Neural Network Modules (nn.Module Equivalent)

**Module Definition:**

```simple
# Define module using class
class LinearLayer:
    weight: Tensor
    bias: Tensor

    fn new(in_features: i64, out_features: i64) -> LinearLayer:
        return LinearLayer {
            weight: Tensor.randn([out_features, in_features]) * 0.01,
            bias: Tensor.zeros([out_features])
        }

    fn forward(self, x: Tensor) -> Tensor:
        return x @ self.weight.transpose([1, 0]) + self.bias

# Use trait for common module interface
trait Module:
    fn forward(self, input: Tensor) -> Tensor
    fn parameters(self) -> List[Tensor]

impl Module for LinearLayer:
    fn forward(self, input: Tensor) -> Tensor:
        return self.forward(input)

    fn parameters(self) -> List[Tensor]:
        return [self.weight, self.bias]

# Compose modules
class MLP:
    layer1: LinearLayer
    layer2: LinearLayer

    fn new(input_dim: i64, hidden_dim: i64, output_dim: i64) -> MLP:
        return MLP {
            layer1: LinearLayer.new(input_dim, hidden_dim),
            layer2: LinearLayer.new(hidden_dim, output_dim)
        }

    fn forward(self, x: Tensor) -> Tensor:
        let hidden = self.layer1.forward(x).relu()
        return self.layer2.forward(hidden)
```

**Design Notes:**

- Use Simple's class system for modules
- Traits provide polymorphism (like Rust's trait system)
- Automatic parameter collection via reflection or explicit methods
- Consider using Simple's metaprogramming for boilerplate reduction

### 3.4 Optimizers

**Optimizer Interface:**

```simple
trait Optimizer:
    fn step(self) async
    fn zero_grad(self)
    fn parameters(self) -> List[Tensor]

class SGD:
    params: List[Tensor]
    lr: f64
    momentum: f64

    fn new(params: List[Tensor], lr: f64, momentum: f64 = 0.0) -> SGD:
        return SGD { params: params, lr: lr, momentum: momentum }

    fn step(self) async:
        for param in self.params:
            if param.grad is not None:
                param.data = param.data - param.grad * self.lr

class Adam:
    params: List[Tensor]
    lr: f64
    beta1: f64
    beta2: f64
    epsilon: f64
    m: Dict[Tensor, Tensor]  # First moment
    v: Dict[Tensor, Tensor]  # Second moment
    t: i64  # Timestep

    fn step(self) async:
        self.t += 1
        for param in self.params:
            if param.grad is None:
                continue

            # Update biased moments
            self.m[param] = self.beta1 * self.m[param] + (1 - self.beta1) * param.grad
            self.v[param] = self.beta2 * self.v[param] + (1 - self.beta2) * param.grad ** 2

            # Bias correction
            let m_hat = self.m[param] / (1 - self.beta1 ** self.t)
            let v_hat = self.v[param] / (1 - self.beta2 ** self.t)

            # Update parameters
            param.data = param.data - self.lr * m_hat / (v_hat.sqrt() + self.epsilon)
```

**Actual Implementation:**

- Optimizers implemented in LibTorch C++ API: [torch::optim](https://docs.pytorch.org/docs/stable/optim.html)
- [Adam implementation](https://github.com/pytorch/pytorch/blob/main/torch/csrc/api/src/optim/adam.cpp) in C++
- Simple wrapper would expose these via FFI

### 3.5 Data Loading

**DataLoader Interface:**

```simple
trait Dataset[T]:
    fn len(self) -> i64
    fn get(self, idx: i64) -> T

class TensorDataset:
    data: Tensor
    labels: Tensor

    fn new(data: Tensor, labels: Tensor) -> TensorDataset:
        return TensorDataset { data: data, labels: labels }

impl Dataset[(Tensor, Tensor)] for TensorDataset:
    fn len(self) -> i64:
        return self.data.shape[0]

    fn get(self, idx: i64) -> (Tensor, Tensor):
        return (self.data[idx], self.labels[idx])

class DataLoader[T]:
    dataset: Dataset[T]
    batch_size: i64
    shuffle: bool
    num_workers: i64

    fn iter(self) -> Iterator[List[T]]:
        # Use Simple's actor model for parallel data loading
        # See section 4.4
        ...
```

**Integration Points:**

- Use Simple's iterator protocol
- Leverage actor model for parallel workers
- GPU tensor transfer via CUDA streams

### 3.6 Model Serialization

**Checkpoint API:**

```simple
# Save model state
let model = MLP.new(784, 256, 10)
let optimizer = Adam.new(model.parameters(), lr: 0.001)

torch.save({
    "model": model.state_dict(),
    "optimizer": optimizer.state_dict(),
    "epoch": epoch
}, "checkpoint.pth")

# Load model state
let checkpoint = torch.load("checkpoint.pth")
model.load_state_dict(checkpoint["model"])
optimizer.load_state_dict(checkpoint["optimizer"])
let epoch = checkpoint["epoch"]
```

**ONNX Export:**

- Use [torch.export-based ONNX exporter](https://docs.pytorch.org/docs/stable/onnx_export.html) (recommended as of 2025)
- Legacy `torch.onnx.export` relies on deprecated TorchScript
- [ONNX metadata](https://docs.pytorch.org/tutorials/beginner/onnx/export_simple_model_to_onnx_tutorial.html) for tracing model origin

```simple
# Export to ONNX
let model = MLP.new(784, 256, 10)
let dummy_input = Tensor.randn([1, 784])

torch.onnx.export(
    model,
    dummy_input,
    "model.onnx",
    export_params: true,
    opset_version: 17,
    do_constant_folding: true,
    input_names: ["input"],
    output_names: ["output"]
)
```

---

## 4. Simple Language Integration

### 4.1 Tensor Representation with Simple's Type System

**Type Safety:**

Simple's type system provides strong guarantees. Tensor types should leverage this:

```simple
# Semantic types for tensor shapes and dtypes
type TensorShape = List[i64]
type DType = enum { F32, F64, I32, I64, U8 }

# Basic tensor type
class Tensor:
    shape: TensorShape
    dtype: DType
    device: Device
    requires_grad: bool
    data: TensorData  # Opaque pointer to LibTorch data

# Shape-checked tensors (using const generics when available)
class Tensor2D[Rows: i64, Cols: i64]:
    # Compile-time shape checking
    ...

# Device-typed tensors
enum Device:
    CPU
    CUDA(device_id: i64)
    MPS  # Apple Metal

# Effect-based tensor operations
fn matmul(a: Tensor, b: Tensor) -> Tensor:
    # Pure function, no side effects
    ...

fn matmul_inplace(a: &mut Tensor, b: Tensor) async:
    # Async GPU operation with mutable borrow
    ...
```

**Integration with Simple's Memory Model:**

From Simple's [memory specification](../spec/memory.md):

- **GC-managed references (`T`)** - Default for tensors
- **Unique pointers (`&T`)** - For exclusive tensor ownership
- **Shared pointers (`*T`)** - For reference-counted sharing
- **Weak pointers (`-T`)** - For caching without ownership

```simple
# GC-managed tensor (default)
let t1: Tensor = Tensor.randn([3, 3])

# Unique ownership for RAII cleanup
let t2: &Tensor = new(&) Tensor.randn([3, 3])

# Shared ownership for cloning
let t3: *Tensor = new* Tensor.randn([3, 3])
let t4 = t3  # Increment refcount

# Weak reference for observation
let t5: -Tensor = weak_of(t3)
```

**Recommendation:** Use GC-managed `Tensor` by default, with explicit pointer types for performance-critical code.

### 4.2 Effect System for GPU Operations

From Simple's [GPU specification](../spec/gpu_simd/README.md):

```simple
# GPU kernel for custom operations
#[gpu]
fn custom_kernel(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] * b[idx] + a[idx]

# Launch from Simple
let ctx = gpu.Context.default()
let a_buf = ctx.alloc_upload(a_data)
let b_buf = ctx.alloc_upload(b_data)
let out_buf = ctx.alloc[f32](1024)

ctx.launch(
    kernel: custom_kernel,
    global_size: [1024],
    local_size: [256],
    args: [a_buf, b_buf, out_buf]
)

# Integration with PyTorch tensors
fn torch_custom_op(a: Tensor, b: Tensor) -> Tensor:
    # Convert PyTorch tensor to Simple GPU buffer
    let a_buf = a.to_gpu_buffer()
    let b_buf = b.to_gpu_buffer()

    # Run custom kernel
    ctx.launch(custom_kernel, ...)

    # Convert back to PyTorch tensor
    return Tensor.from_gpu_buffer(out_buf)
```

**Effect System Benefits:**

1. **Async/Await** - GPU operations are naturally async
2. **Effect Tracking** - Compiler knows which operations may block
3. **Concurrency Safety** - No data races in GPU code

### 4.3 Actor Model for Distributed Training

From Simple's [concurrency specification](../spec/concurrency.md):

```simple
# Distributed data parallel training
actor TrainingWorker:
    state:
        model: MLP
        optimizer: Adam
        rank: i64
        world_size: i64

    on TrainBatch(data: Tensor, labels: Tensor) async:
        # Forward pass
        let output = self.model.forward(data)
        let loss = cross_entropy(output, labels)

        # Backward pass
        loss.backward()

        # All-reduce gradients across workers
        for param in self.model.parameters():
            all_reduce(param.grad, op: :sum)
            param.grad = param.grad / self.world_size

        # Update parameters
        self.optimizer.step()
        self.optimizer.zero_grad()

    on GetModel(reply_to: Pid) async:
        send reply_to, self.model

# Spawn workers
let workers: List[Pid] = []
for rank in 0..world_size:
    let worker = spawn_actor(TrainingWorker.new(rank, world_size))
    workers.push(worker)

# Distribute batches
for (batch_idx, (data, labels)) in train_loader.enumerate():
    let worker = workers[batch_idx % world_size]
    send worker, TrainBatch(data, labels)
```

**Integration with torch.distributed:**

- Map Simple actors to torch.distributed process groups
- Use NCCL backend for GPU communication
- Simple's actor model provides clean abstraction over MPI/NCCL

### 4.4 Memory Management: PyTorch Reference Counting vs Simple's GC

**Challenge:** PyTorch uses reference counting, Simple uses GC.

**Solution Strategies:**

1. **Opaque Handles** - Wrap LibTorch tensors in Simple objects
   ```simple
   class Tensor:
       handle: *mut TorchTensor  # Opaque pointer to LibTorch tensor

       fn destroy(self):
           # Decrement LibTorch refcount
           torch_tensor_free(self.handle)
   ```

2. **GC Integration** - Register PyTorch allocations with Simple's GC
   ```simple
   # When creating tensor from LibTorch
   let torch_ptr = torch_randn([3, 3])
   let tensor = Tensor { handle: torch_ptr }

   # Register finalizer with GC
   gc.register_finalizer(tensor, \t: torch_tensor_free(t.handle))
   ```

3. **Manual Lifetime Management** - Use `&Tensor` for RAII
   ```simple
   fn train_step(model: &Model, data: &Tensor) -> &Tensor:
       # All tensors freed when function returns
       let output = new(&) model.forward(data)
       let loss = new(&) cross_entropy(output, labels)
       loss.backward()
       return move loss
   ```

**Recommendation:** Combine approaches - GC for user-facing API, manual management for performance-critical code.

---

## 5. Implementation Strategy

### 5.1 Direct LibTorch FFI Bindings

**Architecture:**

```
Simple Code
    ↓
LibTorch C++ API (FFI)
    ↓
ATen/Autograd/CUDA
    ↓
Hardware (CPU/GPU)
```

**Advantages:**

- No Python dependency at runtime
- Better performance (no interpreter overhead)
- Type safety at compile time
- Direct access to LibTorch features

**Disadvantages:**

- Some Python-only features unavailable (data augmentation, certain models)
- Need to manually track LibTorch C++ API updates
- More boilerplate for FFI declarations

**Implementation Steps:**

1. **Generate FFI Bindings** - Use bindgen-like tool or manual declarations
   ```simple
   # In simple/std_lib/src/torch/tensor.spl
   extern "C++" from "libtorch":
       fn torch_randn(shape: *i64, ndim: i64) -> *mut TorchTensor
       fn torch_add(a: *mut TorchTensor, b: *mut TorchTensor) -> *mut TorchTensor
       fn torch_matmul(a: *mut TorchTensor, b: *mut TorchTensor) -> *mut TorchTensor
       fn torch_backward(tensor: *mut TorchTensor)
       fn torch_tensor_free(tensor: *mut TorchTensor)
   ```

2. **Wrap in Safe API** - Provide Simple-friendly interface
   ```simple
   class Tensor:
       handle: *mut TorchTensor

       fn randn(shape: List[i64]) -> Tensor:
           let shape_ptr = shape.as_ptr()
           let torch_ptr = torch_randn(shape_ptr, shape.len())
           return Tensor { handle: torch_ptr }

       fn add(self, other: Tensor) -> Tensor:
           let result_ptr = torch_add(self.handle, other.handle)
           return Tensor { handle: result_ptr }

       # Implement drop/finalizer
       fn destroy(self):
           torch_tensor_free(self.handle)
   ```

3. **Build System Integration** - Link against LibTorch
   ```toml
   # simple.toml
   [dependencies]
   libtorch = { path = "/path/to/libtorch", version = "2.9" }

   [build]
   link_libs = ["torch", "c10"]
   include_dirs = ["/path/to/libtorch/include"]
   ```

### 5.2 Python Bridge Layer (When Needed)

**Use Cases for Python Bridge:**

- Python-specific features (torchvision transforms, HuggingFace models)
- Prototyping before LibTorch binding exists
- Legacy codebases with Python dependencies

**Architecture:**

```
Simple Code
    ↓
LibTorch FFI (core ops)
    ↓  ↘
    ↓   CPython C API (bridge)
    ↓       ↓
    ↓   Python PyTorch (optional features)
    ↓       ↓
ATen/Autograd/CUDA
    ↓
Hardware
```

**Implementation:**

```simple
# Python bridge using CPython C API
extern "C" from "python":
    fn Py_Initialize()
    fn PyRun_SimpleString(code: *const u8) -> i32
    fn PyImport_ImportModule(name: *const u8) -> *mut PyObject

class PythonBridge:
    initialized: bool = false
    torch_module: *mut PyObject

    fn init():
        if not self.initialized:
            Py_Initialize()
            self.torch_module = PyImport_ImportModule("torch")
            self.initialized = true

    fn call_python_transform(tensor: Tensor, transform: str) -> Tensor:
        # Convert Simple tensor to Python tensor via DLPack
        let py_tensor = tensor.to_dlpack()

        # Call Python function
        let py_result = PyObject_CallMethod(
            self.torch_module,
            transform,
            py_tensor
        )

        # Convert back via DLPack
        return Tensor.from_dlpack(py_result)
```

**Trade-offs:**

- Adds Python runtime dependency
- GIL contention in multi-threaded code
- Slower than pure LibTorch
- More complex deployment

**Recommendation:** Use sparingly, prefer pure LibTorch bindings where possible.

### 5.3 Build System Integration

**Finding PyTorch Libraries:**

```simple
# Build script (build.spl)
fn find_pytorch() -> PathBuf:
    # Try pkg-config
    if let Some(path) = run("pkg-config --libs torch"):
        return path

    # Try common install locations
    let common_paths = [
        "/usr/local/lib/python3.x/site-packages/torch",
        "/opt/libtorch",
        "~/.local/lib/python3.x/site-packages/torch"
    ]

    for path in common_paths:
        if path.exists():
            return path

    # Try python -c "import torch; print(torch.__path__)"
    let torch_path = run("python -c 'import torch; print(torch.__path__[0])'")
    return PathBuf.new(torch_path)

# Use in simple.toml
[build]
script = "build.spl"
```

**Linking Strategy:**

- Dynamic linking for flexibility: `-ltorch -lc10 -ltorch_cpu -ltorch_cuda`
- Static linking for deployment: Link `.a` archives
- RPATH configuration: `$ORIGIN/../lib` for relocatable binaries

### 5.4 GPU Memory Management

**Strategy:**

```simple
# GPU memory pool managed by LibTorch
class TorchAllocator:
    fn alloc(size: usize, device: Device) -> *mut u8:
        # Delegate to LibTorch's caching allocator
        return torch_alloc(size, device.id())

    fn free(ptr: *mut u8, device: Device):
        torch_free(ptr, device.id())

# Integration with Simple's GPU backend
impl GPUAllocator for TorchAllocator:
    fn alloc_device(size: usize) -> DevicePtr:
        return DevicePtr { ptr: self.alloc(size, Device.CUDA(0)) }
```

**Memory Transfer:**

```simple
# Zero-copy when possible
fn tensor_to_gpu_buffer(tensor: Tensor) -> gpu.Buffer[f32]:
    if tensor.device == Device.CUDA:
        # Already on GPU, wrap existing memory
        return gpu.Buffer.from_ptr(tensor.data_ptr(), tensor.numel())
    else:
        # Copy to GPU
        let buf = gpu_ctx.alloc[f32](tensor.numel())
        buf.upload(tensor.to_vec())
        return buf

# Reverse direction
fn gpu_buffer_to_tensor(buf: gpu.Buffer[f32], shape: List[i64]) -> Tensor:
    # Wrap GPU buffer as PyTorch tensor
    return Tensor.from_device_ptr(buf.ptr(), shape, Device.CUDA(0))
```

### 5.5 Error Handling Strategy

**PyTorch Error Types:**

```simple
enum TorchError:
    ShapeMismatch(expected: TensorShape, got: TensorShape)
    DeviceMismatch(expected: Device, got: Device)
    DTypeMismatch(expected: DType, got: DType)
    OutOfMemory(requested: usize, available: usize)
    CUDAError(code: i32, msg: str)
    BackendError(msg: str)

# Result types for fallible operations
fn matmul(a: Tensor, b: Tensor) -> Result[Tensor, TorchError]:
    if a.shape[1] != b.shape[0]:
        return Err(TorchError.ShapeMismatch(
            expected: [a.shape[0], b.shape[0]],
            got: [a.shape[0], a.shape[1]]
        ))

    # Call LibTorch
    let result_ptr = torch_matmul(a.handle, b.handle)
    if result_ptr.is_null():
        return Err(TorchError.BackendError("matmul failed"))

    return Ok(Tensor { handle: result_ptr })
```

**Exception Translation:**

```simple
# Catch C++ exceptions from LibTorch
extern "C++" fn torch_matmul_safe(
    a: *mut TorchTensor,
    b: *mut TorchTensor,
    error_out: *mut CString
) -> *mut TorchTensor

fn matmul(a: Tensor, b: Tensor) -> Result[Tensor, TorchError]:
    let error_msg = CString.empty()
    let result_ptr = torch_matmul_safe(a.handle, b.handle, &mut error_msg)

    if result_ptr.is_null():
        return Err(TorchError.BackendError(error_msg.to_str()))

    return Ok(Tensor { handle: result_ptr })
```

### 5.6 Type Safety Guarantees

**Compile-Time Checks:**

```simple
# Shape checking (when using const generics)
fn matmul<M: i64, N: i64, K: i64>(
    a: Tensor2D[M, K],
    b: Tensor2D[K, N]
) -> Tensor2D[M, N]:
    # Shape compatibility enforced at compile time
    ...

# Device checking
fn cross_entropy(
    predictions: Tensor[device: Device],
    labels: Tensor[device: Device]
) -> Tensor[device: Device]:
    # Compile error if devices don't match
    ...
```

**Runtime Checks:**

```simple
# Runtime shape validation with clear errors
fn matmul(a: Tensor, b: Tensor) -> Result[Tensor, TorchError]:
    check_shapes(a.shape, b.shape)?
    check_devices(a.device, b.device)?
    check_dtypes(a.dtype, b.dtype)?

    return torch_matmul_impl(a, b)
```

---

## 6. Performance Considerations

### 6.1 Minimizing Python/Simple Boundary Crossings

**Problem:** Each FFI call has overhead (argument marshalling, stack management).

**Solutions:**

1. **Batch Operations** - Combine multiple ops into single call
   ```simple
   # Bad: Multiple small calls
   for i in 0..1000:
       result = tensor[i] * 2

   # Good: Single vectorized call
   result = tensor * 2
   ```

2. **JIT Compilation** - Use TorchScript or torch.compile
   ```simple
   # Mark functions for JIT compilation
   #[torch_jit]
   fn fused_ops(x: Tensor, y: Tensor) -> Tensor:
       return (x + y).relu().sigmoid()

   # Compiles to optimized graph, single FFI call
   let result = fused_ops(a, b)
   ```

3. **Custom Operators** - Implement hot paths in C++/CUDA
   ```simple
   # Define custom op in C++
   extern "C++" fn my_custom_op(a: *mut TorchTensor) -> *mut TorchTensor

   # Register with PyTorch
   torch.library.custom_op("mylib::custom_op", my_custom_op)
   ```

### 6.2 Tensor Memory Layout Compatibility

**Challenge:** Simple arrays may have different layout than PyTorch tensors.

**Solutions:**

1. **Contiguous Layout** - Ensure tensors are contiguous before transfer
   ```simple
   fn to_simple_array(tensor: Tensor) -> Array[f32]:
       # Ensure contiguous layout
       let contig = tensor.contiguous()

       # Zero-copy if possible
       if contig.data_ptr() == tensor.data_ptr():
           return Array.from_ptr(contig.data_ptr(), contig.numel())
       else:
           # Need to copy
           return contig.to_vec().to_array()
   ```

2. **Channels-Last Format** - Respect memory format
   ```simple
   # NHWC layout for convolutions
   let tensor = Tensor.randn([32, 256, 256, 3], memory_format: :channels_last)

   # Simple GPU kernel respects layout
   #[gpu]
   fn process_image(data: &[f32, :channels_last]):
       ...
   ```

### 6.3 Batching and Vectorization

**Batching:**

```simple
# Bad: Process one sample at a time
for sample in dataset:
    output = model(sample)
    loss = criterion(output, label)
    loss.backward()

# Good: Process batches
let dataloader = DataLoader.new(dataset, batch_size: 32)
for (batch_data, batch_labels) in dataloader:
    output = model(batch_data)  # [32, 10]
    loss = criterion(output, batch_labels)
    loss.backward()
```

**Vectorization:**

```simple
# Use PyTorch's vectorized operations
let predictions = model(batch)  # [32, 10]
let probs = softmax(predictions, dim: 1)  # Vectorized over batch
let max_probs = probs.max(dim: 1)  # Vectorized
```

### 6.4 GPU Kernel Launch Overhead

**Problem:** Small GPU operations have high overhead.

**Solutions:**

1. **Kernel Fusion** - Combine multiple kernels
   ```simple
   # Bad: Three kernel launches
   let a = x + y
   let b = a * z
   let c = b.relu()

   # Good: Single fused kernel via torch.compile
   #[torch_jit]
   fn fused(x: Tensor, y: Tensor, z: Tensor) -> Tensor:
       return ((x + y) * z).relu()
   ```

2. **Stream Management** - Overlap computation and transfer
   ```simple
   let stream1 = cuda.Stream.new()
   let stream2 = cuda.Stream.new()

   # Overlap H2D transfer with computation
   with stream1:
       tensor1.cuda()

   with stream2:
       let result = model(tensor2)

   cuda.synchronize()
   ```

3. **Persistent Kernels** - Reuse kernel instances
   ```simple
   # Cache compiled kernels
   let kernel = compile_kernel(custom_op)

   for batch in dataloader:
       kernel.launch(batch)  # No recompilation
   ```

---

## 7. Zero-Copy Data Sharing

### 7.1 DLPack Protocol

**Overview:** [DLPack](https://dmlc.github.io/dlpack/latest/python_spec.html) is the de facto standard for zero-copy tensor exchange between frameworks.

**Key Features:**

- Stable in-memory data structure
- Cross-framework support: PyTorch, TensorFlow, JAX, CuPy, etc.
- Device support: CPU, CUDA, ROCm, Metal
- Zero-copy when possible
- [Python array API standard](https://data-apis.org/array-api/latest/design_topics/data_interchange.html) primary protocol

**DLPack Structure:**

```simple
# DLPack managed tensor structure
struct DLManagedTensor:
    dl_tensor: DLTensor
    manager_ctx: *mut void
    deleter: fn(*mut DLManagedTensor)

struct DLTensor:
    data: *mut void
    device: DLDevice
    ndim: i32
    dtype: DLDataType
    shape: *mut i64
    strides: *mut i64
    byte_offset: u64

struct DLDevice:
    device_type: DLDeviceType  # CPU=1, CUDA=2, etc.
    device_id: i32

enum DLDeviceType:
    CPU = 1
    CUDA = 2
    CUDAHost = 3
    OpenCL = 4
    Vulkan = 7
    Metal = 8
    VPI = 9
    ROCM = 10
```

### 7.2 Implementing DLPack for Simple

**Export Simple Tensor to DLPack:**

```simple
fn tensor_to_dlpack(tensor: Tensor) -> DLManagedTensor:
    let dl_tensor = DLTensor {
        data: tensor.data_ptr(),
        device: DLDevice {
            device_type: match tensor.device:
                Device.CPU => DLDeviceType.CPU,
                Device.CUDA(id) => DLDeviceType.CUDA,
            device_id: tensor.device.id()
        },
        ndim: tensor.ndim(),
        dtype: tensor_dtype_to_dl(tensor.dtype),
        shape: tensor.shape.as_ptr(),
        strides: tensor.strides.as_ptr(),
        byte_offset: 0
    }

    # Create managed tensor with deleter
    return DLManagedTensor {
        dl_tensor: dl_tensor,
        manager_ctx: tensor.handle as *mut void,
        deleter: \managed:
            let tensor_ptr = managed.manager_ctx as *mut TorchTensor
            torch_tensor_free(tensor_ptr)
    }
```

**Import DLPack to Simple Tensor:**

```simple
fn tensor_from_dlpack(managed: *mut DLManagedTensor) -> Tensor:
    let dl = managed.dl_tensor

    # Create PyTorch tensor from DLPack
    let torch_ptr = torch_from_dlpack(managed)

    return Tensor {
        handle: torch_ptr,
        shape: Array.from_ptr(dl.shape, dl.ndim),
        device: device_from_dl(dl.device),
        dtype: dtype_from_dl(dl.dtype),
        requires_grad: false
    }
```

**FFI Bindings:**

```simple
extern "C++" from "libtorch":
    fn torch_from_dlpack(managed: *mut DLManagedTensor) -> *mut TorchTensor
    fn torch_to_dlpack(tensor: *mut TorchTensor) -> *mut DLManagedTensor
```

### 7.3 Zero-Copy Examples

**PyTorch ↔ Simple:**

```simple
# Simple tensor → PyTorch tensor (zero-copy)
let simple_tensor = Tensor.randn([100, 100])
let dlpack = simple_tensor.to_dlpack()
let torch_tensor = torch.from_dlpack(dlpack)  # No copy!

# PyTorch tensor → Simple tensor (zero-copy)
let torch_tensor = torch.randn([100, 100])
let dlpack = torch_tensor.to_dlpack()
let simple_tensor = Tensor.from_dlpack(dlpack)  # No copy!
```

**CUDA Tensors:**

```simple
# GPU tensor sharing (zero-copy)
let cuda_tensor = Tensor.randn([1000, 1000], device: :cuda)
let dlpack = cuda_tensor.to_dlpack()

# Use in Simple GPU kernel
let gpu_buf = gpu.Buffer.from_dlpack(dlpack)
ctx.launch(my_kernel, args: [gpu_buf])

# Convert back to tensor
let result = Tensor.from_dlpack(gpu_buf.to_dlpack())
```

**Cross-Framework Pipeline:**

```simple
# Simple → PyTorch → JAX → Simple (all zero-copy)
let simple_data = load_data()  # Simple tensor

# Pass to PyTorch model
let torch_data = torch.from_dlpack(simple_data.to_dlpack())
let torch_output = model(torch_data)

# Pass to JAX for post-processing
let jax_output = jax.from_dlpack(torch_output.to_dlpack())
let processed = jax_transform(jax_output)

# Back to Simple
let final = Tensor.from_dlpack(processed.to_dlpack())
```

### 7.4 Memory Ownership and Lifetime

**Challenge:** Who owns the memory after DLPack transfer?

**Solution:** Use `deleter` callback in `DLManagedTensor`

```simple
# Transfer ownership to recipient
fn transfer_tensor(tensor: Tensor) -> DLManagedTensor:
    let managed = tensor.to_dlpack()

    # Managed tensor owns the data
    # Deleter will free when recipient is done

    return managed

# Borrow without ownership transfer
fn borrow_tensor(tensor: &Tensor) -> DLManagedTensor:
    let managed = tensor.to_dlpack()

    # Override deleter to not free
    managed.deleter = \m: ()  # No-op deleter

    return managed
```

---

## 8. Recommended Architecture

### 8.1 Three-Layer Design

```
┌─────────────────────────────────────────────┐
│   High-Level Simple API (torch.spl)        │
│   - Tensor, Module, Optimizer               │
│   - Pythonic syntax with Simple types      │
│   - Safe wrappers, error handling           │
└─────────────────┬───────────────────────────┘
                  │
┌─────────────────▼───────────────────────────┐
│   Mid-Level FFI Bindings (torch_ffi.spl)   │
│   - Direct LibTorch C++ API calls          │
│   - Memory management, refcounting          │
│   - DLPack conversions                      │
└─────────────────┬───────────────────────────┘
                  │
┌─────────────────▼───────────────────────────┐
│   LibTorch C++ API                          │
│   - ATen tensor operations                  │
│   - Autograd engine                         │
│   - CUDA/GPU backends                       │
└─────────────────────────────────────────────┘
```

**Optional Python Bridge (for specific features):**

```
┌─────────────────────────────────────────────┐
│   High-Level Simple API                    │
└────┬──────────────────────────────┬─────────┘
     │                              │
     ▼                              ▼
┌──────────┐              ┌──────────────────┐
│ LibTorch │              │ Python Bridge    │
│ FFI      │              │ (CPython C API)  │
└──────────┘              └─────────┬────────┘
                                    │
                          ┌─────────▼────────┐
                          │ Python PyTorch   │
                          │ (transforms,     │
                          │  models, etc.)   │
                          └──────────────────┘
```

### 8.2 Module Organization

```
simple/std_lib/src/torch/
├── __init__.spl          # Re-exports all public APIs
├── tensor.spl            # Tensor type and operations
├── autograd.spl          # Gradient computation
├── nn/                   # Neural network modules
│   ├── __init__.spl
│   ├── module.spl        # Module trait
│   ├── linear.spl        # Linear layers
│   ├── conv.spl          # Convolutional layers
│   ├── activation.spl    # ReLU, Sigmoid, etc.
│   └── loss.spl          # Loss functions
├── optim/                # Optimizers
│   ├── __init__.spl
│   ├── optimizer.spl     # Optimizer trait
│   ├── sgd.spl
│   ├── adam.spl
│   └── adamw.spl
├── data/                 # Data loading
│   ├── __init__.spl
│   ├── dataset.spl       # Dataset trait
│   ├── dataloader.spl    # DataLoader
│   └── transforms.spl    # Data augmentation
├── cuda/                 # GPU support
│   ├── __init__.spl
│   ├── device.spl        # Device management
│   ├── stream.spl        # CUDA streams
│   └── memory.spl        # Memory management
├── distributed/          # Distributed training
│   ├── __init__.spl
│   ├── ddp.spl           # DistributedDataParallel
│   ├── fsdp.spl          # Fully Sharded Data Parallel
│   └── backend.spl       # Communication backends
├── ffi/                  # Low-level FFI bindings
│   ├── __init__.spl
│   ├── tensor_ffi.spl    # Raw LibTorch calls
│   ├── autograd_ffi.spl
│   ├── nn_ffi.spl
│   └── dlpack.spl        # DLPack support
└── python_bridge/        # Optional Python interop
    ├── __init__.spl
    └── cpython.spl       # CPython C API bindings
```

### 8.3 API Design Guidelines

**1. Follow Simple Conventions:**

```simple
# Use Simple's naming (snake_case for functions/variables)
fn create_tensor(shape: List[i64]) -> Tensor

# Not PyTorch's (camelCase)
# fn createTensor(shape: List[i64]) -> Tensor
```

**2. Leverage Simple's Type System:**

```simple
# Use semantic types
type TensorShape = List[i64]
type LearningRate = f64

fn linear(in_features: i64, out_features: i64) -> Linear
```

**3. Use Simple's Error Handling:**

```simple
# Result types for fallible operations
fn matmul(a: Tensor, b: Tensor) -> Result[Tensor, TorchError]

# Not exceptions
```

**4. Integrate with Simple's Effect System:**

```simple
# Mark GPU operations as async
fn matmul_cuda(a: Tensor, b: Tensor) async -> Tensor
```

**5. Provide Builder Patterns:**

```simple
# PyTorch-style
let dataloader = DataLoader.new(
    dataset: dataset,
    batch_size: 32,
    shuffle: true,
    num_workers: 4
)

# Simple builder (alternative)
let dataloader = DataLoader.builder()
    .dataset(dataset)
    .batch_size(32)
    .shuffle(true)
    .num_workers(4)
    .build()
```

### 8.4 Implementation Priorities

**Phase 1: Core Tensor Operations**

- [ ] Tensor creation (zeros, ones, randn, etc.)
- [ ] Basic operations (+, -, *, /, @)
- [ ] Shape operations (reshape, transpose, view)
- [ ] Reductions (sum, mean, max, min)
- [ ] Device management (cpu, cuda, to)
- [ ] DLPack support

**Phase 2: Autograd**

- [ ] Gradient tracking (requires_grad)
- [ ] Backward pass (.backward())
- [ ] Gradient access (.grad)
- [ ] Gradient context managers (no_grad, enable_grad)

**Phase 3: Neural Networks**

- [ ] Module trait
- [ ] Linear layers
- [ ] Convolutional layers
- [ ] Activation functions
- [ ] Loss functions
- [ ] Parameter management

**Phase 4: Training Infrastructure**

- [ ] Optimizers (SGD, Adam)
- [ ] Data loading (Dataset, DataLoader)
- [ ] Training loops
- [ ] Model serialization

**Phase 5: Advanced Features**

- [ ] Distributed training
- [ ] Mixed precision training
- [ ] Custom operators
- [ ] TorchScript/torch.compile integration

**Phase 6: Optional Python Bridge**

- [ ] CPython C API bindings
- [ ] Python object marshalling
- [ ] GIL management
- [ ] torchvision/torchaudio integration

---

## 9. Conclusion

### 9.1 Summary of Recommendations

**Primary Approach:** Direct LibTorch C++ API FFI bindings

**Rationale:**

1. **Performance** - No Python interpreter overhead
2. **Type Safety** - Compile-time checking in Simple
3. **Deployment** - No Python runtime dependency
4. **Integration** - Clean mapping to Simple's type system and effect system

**Optional Python Bridge:**

- Use for Python-specific features (torchvision, HuggingFace)
- Keep isolated from core API
- Document Python dependency clearly

**Zero-Copy Data Sharing:**

- Implement DLPack protocol for interoperability
- Enable seamless integration with Simple's GPU backend
- Support cross-framework pipelines

### 9.2 Key Design Decisions

| Aspect | Decision | Rationale |
|--------|----------|-----------|
| **Primary API** | LibTorch C++ FFI | Performance, type safety, no Python dependency |
| **Tensor Memory** | GC-managed with manual option | Simple default, RAII for perf-critical code |
| **Gradient Computation** | Explicit .backward() | Matches PyTorch, clear control flow |
| **GPU Operations** | Async effect | Natural fit for Simple's effect system |
| **Distributed Training** | Actor-based | Leverages Simple's concurrency model |
| **Data Interchange** | DLPack | Standard protocol, zero-copy |
| **Error Handling** | Result types | Simple convention, explicit handling |
| **Python Bridge** | Optional, isolated | For specific features only |

### 9.3 Next Steps

1. **Prototype Core API** - Implement tensor creation and basic operations
2. **Benchmark Performance** - Compare with Python PyTorch
3. **Document API** - Write comprehensive API docs
4. **Implement Autograd** - Add gradient tracking and backprop
5. **Build Examples** - Create tutorial notebooks
6. **Test Distributed Training** - Validate actor-based approach
7. **Integrate with Simple GPU** - Ensure seamless GPU kernel interop
8. **Package and Deploy** - Create distributable library

---

## References

### PyTorch Documentation

- [LibTorch C++ API](https://docs.pytorch.org/cppdocs/)
- [LibTorch Stable ABI](https://docs.pytorch.org/docs/stable/notes/libtorch_stable_abi.html)
- [C++ Frontend Tutorial](https://docs.pytorch.org/tutorials/advanced/cpp_frontend.html)
- [ATen Tensor Library Guide](https://www.codegenes.net/blog/pytorch-aten-library/)
- [CUDA Semantics](https://docs.pytorch.org/docs/stable/notes/cuda.html)
- [Understanding CUDA Memory Usage](https://docs.pytorch.org/docs/stable/torch_cuda_memory.html)
- [Tensor Memory Format](https://pytorch.org/blog/tensor-memory-format-matters/)
- [torch.compile Introduction](https://docs.pytorch.org/tutorials/intermediate/torch_compile_tutorial.html)
- [Distributed Training Overview](https://docs.pytorch.org/tutorials/beginner/dist_overview.html)
- [torch.distributed API](https://docs.pytorch.org/docs/stable/distributed.html)
- [Custom C++ and CUDA Operators](https://docs.pytorch.org/tutorials/advanced/cpp_custom_ops.html)
- [torch.library Documentation](https://docs.pytorch.org/docs/stable/library.html)
- [ONNX Export Guide](https://docs.pytorch.org/docs/stable/onnx_export.html)
- [Optimizer API](https://docs.pytorch.org/docs/stable/optim.html)

### Python/C API

- [Extending and Embedding Python](https://docs.python.org/3/extending/index.html)
- [Python/C API Reference](https://docs.python.org/3/c-api/index.html)
- [Embedding Python in C++](https://docs.python.org/3/extending/embedding.html)

### Rust/PyTorch Integration

- [PyO3 Rust Bindings](https://github.com/PyO3/pyo3)
- [PyO3 Documentation](https://pyo3.rs/)
- [tch-rs: Rust PyTorch Bindings](https://github.com/LaurentMazare/tch-rs)
- [pyo3-tch: PyO3 ↔ tch-rs Bridge](https://lib.rs/crates/pyo3-tch)
- [Transformer with PyTorch and Rust](https://jadon.io/blog/pytorch-rust/)

### DLPack and Zero-Copy

- [DLPack Python Specification](https://dmlc.github.io/dlpack/latest/python_spec.html)
- [Python Array API Standard](https://data-apis.org/array-api/latest/design_topics/data_interchange.html)
- [DLPack.jl for Julia](https://github.com/p-zubieta/DLPack.jl)
- [PyCall.jl: Julia ↔ Python](https://github.com/JuliaPy/PyCall.jl)
- [Apache Arrow DLPack Support](https://arrow.apache.org/docs/python/dlpack.html)
- [Zero-Copy Data Sharing via DLPack](https://apxml.com/courses/advanced-jax/chapter-5-jax-interoperability-custom-operations/zero-copy-dlpack)

### Simple Language Specifications

- [GPU and SIMD Specification](../spec/gpu_simd/README.md)
- [Memory and Ownership](../spec/memory.md)
- [Concurrency and Actors](../spec/concurrency.md)
- [FFI/ABI Specification](../spec/ffi_abi.md)
- [Type System](../spec/types.md)

---

**Document Version:** 1.0
**Last Updated:** 2025-12-26
**License:** MIT (consistent with Simple language)
