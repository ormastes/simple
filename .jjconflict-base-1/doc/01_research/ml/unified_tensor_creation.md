# Unified Tensor/Variable Creation API

**Date:** 2026-01-26
**Status:** Research
**Related:** `math_torch_seamless_integration.md`, `pytorch_integration.md`

## Executive Summary

This document explores how to create variables/tensors consistently across three backends:
1. **CPU Native** - Fast, pure Simple arrays (no FFI overhead)
2. **GPU (CUDA/Vulkan)** - Hardware-accelerated compute
3. **PyTorch Tensor** - Full autograd, interop with ML ecosystem

The goal is a **unified API** where the same code works across all backends with minimal changes.

---

## 1. Current State Analysis

### 1.1 Existing Factory Functions

| Location | Factory | Backends | Notes |
|----------|---------|----------|-------|
| `ml/torch/factory.spl` | `zeros`, `ones`, `randn`, `arange` | PyTorch (CPU/CUDA) | Main API |
| `ml/torch/tensor_class.spl` | `Tensor::zeros`, `Tensor::ones` | PyTorch | Static methods |
| `ml/torch/ffi_helpers.spl` | `zeros_1d/2d/3d`, etc. | PyTorch | Optimized variants |
| `std_lib/src/tensor.spl` | `zeros<T>`, `ones<T>`, `randn<T>` | PyTorch (planned) | Generic API |
| `core/array.spl` | `Array::new`, `Array::filled` | Native CPU | Fixed-size only |

### 1.2 Current API Patterns

```simple
# PyTorch factory (current)
val t = torch.zeros([3, 4], dtype: DType::Float32, device: Device::CPU)
val t_gpu = torch.randn([100, 100], device: Device::CUDA(0))

# Native array (current)
val arr = Array::filled(0.0)      # Fixed size at compile time
val arr2 = Array::of([1.0, 2.0])

# Generic tensor (planned)
val t = zeros<f64>([3, 4])        # Backend auto-selected
```

---

## 2. Design Goals

| Goal | Description |
|------|-------------|
| **Unified syntax** | Same `zeros`, `ones`, `randn` everywhere |
| **Backend polymorphism** | Code works on CPU, GPU, or PyTorch |
| **Zero-cost abstraction** | No overhead when backend is known |
| **Gradual adoption** | Can mix backends in same program |
| **Type safety** | Catch dtype/device mismatches at compile time |

---

## 3. Proposed Architecture

### 3.1 Tensor Options (Builder Pattern)

Inspired by PyTorch's C++ [TensorOptions](https://docs.pytorch.org/cppdocs/notes/tensor_creation.html):

```simple
struct TensorOptions:
    """Configuration for tensor creation.

    Builder-style API for specifying dtype, device, and other options.
    """
    dtype: DType = DType::Float32
    device: Device = Device::CPU
    requires_grad: bool = false
    layout: Layout = Layout::Strided
    pinned_memory: bool = false

impl TensorOptions:
    # Builder methods (chainable)
    fn dtype(self, d: DType) -> TensorOptions:
        TensorOptions(dtype: d, ..self)

    fn device(self, d: Device) -> TensorOptions:
        TensorOptions(device: d, ..self)

    fn requires_grad(self, r: bool) -> TensorOptions:
        TensorOptions(requires_grad: r, ..self)

    fn cuda(self, id: i32 = 0) -> TensorOptions:
        self.device(Device::CUDA(id))

    fn cpu(self) -> TensorOptions:
        self.device(Device::CPU)

    fn f32(self) -> TensorOptions:
        self.dtype(DType::Float32)

    fn f64(self) -> TensorOptions:
        self.dtype(DType::Float64)

    fn grad(self) -> TensorOptions:
        self.requires_grad(true)
```

### 3.2 Usage Examples

```simple
# Basic usage with defaults
val a = zeros([3, 4])  # CPU, Float32, no grad

# With options (builder pattern)
val b = zeros([3, 4], opts.cuda().f64().grad())

# Shorthand for common cases
val c = zeros([3, 4], device: cuda(0))
val d = randn([100, 100], dtype: f32, requires_grad: true)

# Default options object
val opts = TensorOptions()
    .dtype(DType::Float64)
    .device(Device::CUDA(0))
    .requires_grad(true)

val W = randn([784, 256], opts)
val b = zeros([256], opts)
```

---

## 4. Backend Abstraction

### 4.1 Backend Trait

```simple
trait TensorBackend:
    """Abstract backend for tensor operations."""

    # Factory methods
    fn zeros(shape: [i64], opts: TensorOptions) -> Self::Tensor
    fn ones(shape: [i64], opts: TensorOptions) -> Self::Tensor
    fn randn(shape: [i64], opts: TensorOptions) -> Self::Tensor
    fn full(shape: [i64], value: f64, opts: TensorOptions) -> Self::Tensor
    fn arange(start: i64, end: i64, step: i64, opts: TensorOptions) -> Self::Tensor
    fn from_data(data: [f64], shape: [i64], opts: TensorOptions) -> Self::Tensor

    # Type associated with this backend
    type Tensor: TensorLike

trait TensorLike:
    """Operations that all tensor types support."""
    fn shape() -> [i64]
    fn dtype() -> DType
    fn device() -> Device
    fn to(device: Device) -> Self
    fn clone() -> Self
```

### 4.2 Backend Implementations

```simple
# Native CPU backend (no FFI, fast for small arrays)
struct NativeBackend

impl TensorBackend for NativeBackend:
    type Tensor = NativeTensor

    fn zeros(shape: [i64], opts: TensorOptions) -> NativeTensor:
        val size = shape.product()
        val data = Vec::filled(size, 0.0)
        NativeTensor(data, shape, opts.dtype)

    fn randn(shape: [i64], opts: TensorOptions) -> NativeTensor:
        val size = shape.product()
        val data = Vec::with_capacity(size)
        for _ in 0..size:
            data.push(random_normal())
        NativeTensor(data, shape, opts.dtype)

# PyTorch backend (full autograd, GPU support)
struct TorchBackend

impl TensorBackend for TorchBackend:
    type Tensor = TorchTensor

    fn zeros(shape: [i64], opts: TensorOptions) -> TorchTensor:
        val handle = rt_torch_zeros(
            shape.data_ptr(),
            shape.len() as i32,
            dtype_code(opts.dtype),
            device_code(opts.device)
        )
        TorchTensor(handle)

# Vulkan/WebGPU backend (cross-platform GPU)
struct GpuBackend

impl TensorBackend for GpuBackend:
    type Tensor = GpuTensor

    fn zeros(shape: [i64], opts: TensorOptions) -> GpuTensor:
        val buffer = gpu_allocate(shape.product() * opts.dtype.byte_size())
        gpu_fill_zeros(buffer)
        GpuTensor(buffer, shape, opts.dtype)
```

---

## 5. Unified Factory Functions

### 5.1 Global Factory with Auto-Backend Selection

```simple
# Global default backend (configurable)
var _default_backend: BackendType = BackendType::PyTorch

fn set_default_backend(backend: BackendType):
    _default_backend = backend

fn get_default_backend() -> BackendType:
    _default_backend

# Unified factory functions
fn zeros(shape: [i64], opts: TensorOptions = TensorOptions()) -> Tensor:
    """Create tensor filled with zeros.

    Backend is selected based on:
    1. Explicit device in opts (CUDA → PyTorch)
    2. requires_grad in opts (true → PyTorch)
    3. Default backend setting

    Example:
        val a = zeros([3, 4])                    # Default backend
        val b = zeros([3, 4], opts.cuda())       # PyTorch CUDA
        val c = zeros([3, 4], opts.grad())       # PyTorch with autograd
    """
    val backend = select_backend(opts)
    match backend:
        BackendType::Native: NativeBackend.zeros(shape, opts).into()
        BackendType::PyTorch: TorchBackend.zeros(shape, opts).into()
        BackendType::Gpu: GpuBackend.zeros(shape, opts).into()

fn ones(shape: [i64], opts: TensorOptions = TensorOptions()) -> Tensor:
    val backend = select_backend(opts)
    match backend:
        BackendType::Native: NativeBackend.ones(shape, opts).into()
        BackendType::PyTorch: TorchBackend.ones(shape, opts).into()
        BackendType::Gpu: GpuBackend.ones(shape, opts).into()

fn randn(shape: [i64], opts: TensorOptions = TensorOptions()) -> Tensor:
    val backend = select_backend(opts)
    match backend:
        BackendType::Native: NativeBackend.randn(shape, opts).into()
        BackendType::PyTorch: TorchBackend.randn(shape, opts).into()
        BackendType::Gpu: GpuBackend.randn(shape, opts).into()
```

### 5.2 Backend Selection Logic

```simple
fn select_backend(opts: TensorOptions) -> BackendType:
    """Select appropriate backend based on options.

    Priority:
    1. CUDA device → PyTorch (only PyTorch supports CUDA autograd)
    2. requires_grad → PyTorch (only PyTorch has autograd)
    3. Large tensor (>1M elements) → PyTorch or GPU
    4. Default backend setting
    """
    # CUDA requires PyTorch
    if opts.device.is_cuda():
        return BackendType::PyTorch

    # Autograd requires PyTorch
    if opts.requires_grad:
        return BackendType::PyTorch

    # Use default
    return get_default_backend()
```

---

## 6. Convenience Shortcuts

### 6.1 Device Constructors

```simple
# Device shortcuts (return TensorOptions)
fn cpu() -> TensorOptions:
    TensorOptions().cpu()

fn cuda(id: i32 = 0) -> TensorOptions:
    TensorOptions().cuda(id)

fn gpu(id: i32 = 0) -> TensorOptions:
    # Auto-select: CUDA if available, else Vulkan/WebGPU
    if cuda_available():
        TensorOptions().cuda(id)
    else:
        TensorOptions().device(Device::Vulkan(id))
```

### 6.2 DType Shortcuts

```simple
# DType shortcuts (return TensorOptions)
fn f16() -> TensorOptions:
    TensorOptions().dtype(DType::Float16)

fn f32() -> TensorOptions:
    TensorOptions().dtype(DType::Float32)

fn f64() -> TensorOptions:
    TensorOptions().dtype(DType::Float64)

fn i32() -> TensorOptions:
    TensorOptions().dtype(DType::Int32)

fn i64() -> TensorOptions:
    TensorOptions().dtype(DType::Int64)

fn bf16() -> TensorOptions:
    TensorOptions().dtype(DType::BFloat16)
```

### 6.3 Combined Shortcuts

```simple
# Common combinations
fn cuda_f32(id: i32 = 0) -> TensorOptions:
    cuda(id).f32()

fn cuda_f16(id: i32 = 0) -> TensorOptions:
    cuda(id).f16()

fn param(dtype: DType = DType::Float32, device: Device = Device::CPU) -> TensorOptions:
    """Options for trainable parameters (requires_grad=true)."""
    TensorOptions(dtype: dtype, device: device, requires_grad: true)
```

---

## 7. Usage Patterns

### 7.1 Simple Computation (Auto Backend)

```simple
import tensor.*

# Backend auto-selected (default: PyTorch for interop)
val A = randn([100, 100])
val B = randn([100, 100])
val C = A @ B  # Matrix multiply
print C.sum()
```

### 7.2 GPU Computation

```simple
import tensor.*

# Explicit CUDA
val A = randn([1000, 1000], cuda())
val B = randn([1000, 1000], cuda())
val C = A @ B  # Runs on GPU
print C.to(cpu()).sum()  # Transfer back for printing
```

### 7.3 Training with Autograd

```simple
import tensor.*

# Parameters with gradients
val W = randn([784, 256], param().cuda())
val b = zeros([256], param().cuda())

# Forward pass (autograd tracks)
fn forward(x: Tensor) -> Tensor:
    m{ W @ x + b }

# Training loop
for batch in data_loader:
    val loss = compute_loss(forward(batch.x), batch.y)
    loss.backward()
    optimizer.step()
```

### 7.4 Native Backend (No FFI Overhead)

```simple
import tensor.*

set_default_backend(BackendType::Native)

# Fast for small arrays, no PyTorch overhead
val small = randn([10, 10])  # Uses native implementation
val result = small @ small.T
```

---

## 8. `like` Pattern (NumPy Interop)

Inspired by [NumPy's `like` parameter](https://numpy.org/doc/stable/user/basics.interoperability.html):

```simple
fn zeros_like(t: Tensor, opts: TensorOptions? = None) -> Tensor:
    """Create zeros with same shape/dtype/device as input.

    If opts provided, overrides input's properties.
    """
    val actual_opts = opts ?? TensorOptions(
        dtype: t.dtype(),
        device: t.device(),
        requires_grad: t.requires_grad()
    )
    zeros(t.shape(), actual_opts)

fn ones_like(t: Tensor, opts: TensorOptions? = None) -> Tensor:
    val actual_opts = opts ?? TensorOptions(
        dtype: t.dtype(),
        device: t.device()
    )
    ones(t.shape(), actual_opts)

fn randn_like(t: Tensor, opts: TensorOptions? = None) -> Tensor:
    val actual_opts = opts ?? TensorOptions(
        dtype: t.dtype(),
        device: t.device()
    )
    randn(t.shape(), actual_opts)

fn empty_like(t: Tensor, opts: TensorOptions? = None) -> Tensor:
    val actual_opts = opts ?? TensorOptions(
        dtype: t.dtype(),
        device: t.device()
    )
    empty(t.shape(), actual_opts)
```

---

## 9. Comparison with Other Frameworks

| Framework | Factory Pattern | Device Spec | Notes |
|-----------|-----------------|-------------|-------|
| **PyTorch** | `torch.zeros(shape, dtype=, device=)` | Keyword args | [Tensor Creation API](https://docs.pytorch.org/cppdocs/notes/tensor_creation.html) |
| **JAX** | `jnp.zeros(shape, dtype=)` + `device_put` | Separate step | [Device Management](https://apxml.com/courses/getting-started-with-jax/chapter-1-introduction-to-jax/jax-device-management) |
| **NumPy** | `np.zeros(shape, dtype=)` | CPU only | [Array Creation](https://numpy.org/doc/stable/reference/generated/numpy.array.html) |
| **TensorFlow** | `tf.zeros(shape, dtype=)` + `with device` | Context manager | Verbose |
| **Simple (proposed)** | `zeros(shape, opts)` | Builder pattern | Unified API |

---

## 10. Implementation Plan

### Phase 1: TensorOptions (1 week)

1. Define `TensorOptions` struct
2. Implement builder methods
3. Add device/dtype shortcuts
4. Tests

### Phase 2: Backend Trait (2 weeks)

1. Define `TensorBackend` trait
2. Implement `TorchBackend` (wrap existing FFI)
3. Implement `NativeBackend` (pure Simple)
4. Backend selection logic

### Phase 3: Unified Factory (1 week)

1. Implement `zeros`, `ones`, `randn`, etc.
2. Add `*_like` functions
3. Integration tests

### Phase 4: GPU Backend (2 weeks)

1. Vulkan/WebGPU buffer management
2. GPU compute shaders for fill operations
3. Device-to-device transfers

---

## 11. API Summary

### Factory Functions

| Function | Description | Example |
|----------|-------------|---------|
| `zeros(shape, opts)` | Fill with 0 | `zeros([3,4])` |
| `ones(shape, opts)` | Fill with 1 | `ones([3,4], cuda())` |
| `full(shape, val, opts)` | Fill with value | `full([3,4], 3.14)` |
| `randn(shape, opts)` | Normal random | `randn([100], f64())` |
| `rand(shape, opts)` | Uniform [0,1) | `rand([10,10])` |
| `randint(low, high, shape, opts)` | Integer random | `randint(0, 10, [5])` |
| `arange(start, end, step, opts)` | Range | `arange(0, 10, 2)` |
| `linspace(start, end, n, opts)` | Linear space | `linspace(0, 1, 100)` |
| `eye(n, opts)` | Identity matrix | `eye(4)` |
| `from_data(data, shape, opts)` | From array | `from_data([1,2,3,4], [2,2])` |

### Option Shortcuts

| Shortcut | Equivalent |
|----------|------------|
| `cpu()` | `TensorOptions().device(Device::CPU)` |
| `cuda(id)` | `TensorOptions().device(Device::CUDA(id))` |
| `gpu(id)` | Auto-select GPU backend |
| `f32()` | `TensorOptions().dtype(DType::Float32)` |
| `f64()` | `TensorOptions().dtype(DType::Float64)` |
| `param()` | `TensorOptions().requires_grad(true)` |
| `cuda_f32(id)` | `cuda(id).f32()` |

### Like Functions

| Function | Description |
|----------|-------------|
| `zeros_like(t, opts?)` | Zeros matching t's properties |
| `ones_like(t, opts?)` | Ones matching t's properties |
| `randn_like(t, opts?)` | Random matching t's properties |
| `empty_like(t, opts?)` | Uninitialized matching t's properties |

---

## 12. Open Questions

1. **Backend polymorphism**: Should `Tensor` be an enum or trait object?
2. **Autograd boundary**: Can native backend tensors participate in autograd?
3. **Memory management**: How to handle cross-backend transfers efficiently?
4. **Compilation**: Should backend be selected at compile time or runtime?
5. **Interop**: How to convert between backends seamlessly?

---

## 13. References

- [PyTorch Tensor Creation API (C++)](https://docs.pytorch.org/cppdocs/notes/tensor_creation.html)
- [JAX Device Management](https://apxml.com/courses/getting-started-with-jax/chapter-1-introduction-to-jax/jax-device-management)
- [NumPy Interoperability](https://numpy.org/doc/stable/user/basics.interoperability.html)
- [NumPy `__array_function__` Protocol](https://numpy.org/doc/stable/user/basics.dispatch.html)
- [PyTorch Meta Device](https://docs.pytorch.org/docs/stable/meta.html)

---

## Appendix A: Full Example

```simple
import tensor.*
import ml.optim.*

# Configure for GPU training
set_default_backend(BackendType::PyTorch)
val device = cuda(0)

# Model parameters
val W1 = randn([784, 256], param().cuda())
val b1 = zeros([256], param().cuda())
val W2 = randn([256, 10], param().cuda())
val b2 = zeros([10], param().cuda())

fn forward(x: Tensor) -> Tensor:
    m{
        h = relu(W1 @ x + b1)
        W2 @ h + b2
    }

fn compute_loss(logits: Tensor, targets: Tensor) -> Tensor:
    cross_entropy(logits, targets)

# Training
val optimizer = Adam([W1, b1, W2, b2], lr: 0.001)

for epoch in 0..10:
    for (x, y) in train_loader:
        # Move data to GPU
        val x_gpu = x.to(device)
        val y_gpu = y.to(device)

        # Forward + backward
        optimizer.zero_grad()
        val loss = compute_loss(forward(x_gpu), y_gpu)
        loss.backward()
        optimizer.step()

    # Validation (no grad)
    with no_grad():
        val val_acc = evaluate(val_loader, device)
        print "Epoch {epoch}: val_acc = {val_acc:.2%}"
```
