# Unified Tensor Interface Design

**Date:** 2026-01-26
**Status:** Research / Design Proposal
**Related:** `unified_tensor_creation.md`, `tensor_init_comparison.md`

## Executive Summary

Design a **unified interface** for tensor creation and operations that works consistently across:
- Native CPU arrays
- GPU (CUDA) arrays
- PyTorch tensors (with autograd)

Using **suffix notation** and **configuration-based defaults** for a seamless experience.

---

## 1. Suffix Notation for Type and Device

### 1.1 Existing Simple Suffix Patterns

Simple already supports suffix notation:

```simple
# Numeric type suffixes (existing) - BOTH styles supported
val a = 42i32                       # Attached style (Rust)
val a = 42_i32                      # Underscore style
val b = 3.14f64                     # Attached
val b = 3.14_f64                    # Underscore
val c = 0f32                        # Zero as f32
val c = 0_f32                       # Same, underscore style

# Unit literals (underscore style)
val d = 100_km                      # Length unit
val e = 2_hr                        # Time unit

# String type suffixes (existing)
val path = "/etc/config"_file       # File path
val regex = "[a-z]+"_re             # Regex pattern
```

**Both `0f32` and `0_f32` are valid and equivalent.**

### 1.2 Suffix Style Rules

**Two equivalent suffix styles:**

| Style | Scalar | Array | Description |
|-------|--------|-------|-------------|
| **Attached** | `0f32` | `[1,2,3]f32` | No underscore (Rust-like) |
| **Underscore** | `0_f32` | `[1,2,3]_f32` | With underscore (readable) |

```simple
# Scalars - both valid
val a = 0f32                        # Attached
val a = 0_f32                       # Underscore (same)
val b = 3.14f64                     # Attached
val b = 3.14_f64                    # Underscore (same)

# Arrays - both valid
val arr = [1, 2, 3]f32              # Attached
val arr = [1, 2, 3]_f32             # Underscore (same)

# Multi-part suffix - underscore between parts
val arr = [1, 2, 3]f32_gpu          # Type attached, device underscore
val arr = [1, 2, 3]_f32_gpu         # All underscore (recommended)
```

**Recommendation:** Use underscore style for readability, especially with multiple suffixes.

### 1.3 Proposed Array/Tensor Suffix Notation

Extend suffix notation to arrays:

```simple
# ============================================
# Type suffix for arrays
# ============================================
val arr = [1, 2, 3, 4]_f64          # [f64] array
val arr = [1, 2, 3, 4]_f32          # [f32] array
val arr = [1, 2, 3, 4]_i64          # [i64] array

# ============================================
# Device suffix
# ============================================
val arr = [1, 2, 3, 4]_cpu          # CPU (native or torch)
val arr = [1, 2, 3, 4]_gpu          # Default GPU
val arr = [1, 2, 3, 4]_cuda         # CUDA GPU
val arr = [1, 2, 3, 4]_cuda0        # CUDA device 0
val arr = [1, 2, 3, 4]_cuda1        # CUDA device 1

# ============================================
# Combined: type + device
# ============================================
val arr = [1, 2, 3, 4]_f64_cpu      # f64 on CPU
val arr = [1, 2, 3, 4]_f32_gpu      # f32 on GPU
val arr = [1, 2, 3, 4]_f32_cuda     # f32 on CUDA
val arr = [1, 2, 3, 4]_f16_cuda0    # f16 on CUDA:0

# ============================================
# Trainable (requires_grad) suffix
# ============================================
val W = [[...]]_f32_tr              # Trainable, CPU
val W = [[...]]_f32_tr_gpu          # Trainable, GPU
val W = [[...]]_f32_tr_cuda         # Trainable, CUDA
val b = [0, 0, 0]_f32_tr_cuda0      # Trainable, CUDA:0

# ============================================
# Backend selection suffix
# ============================================
val arr = [1, 2, 3]_native          # Force native backend
val arr = [1, 2, 3]_torch           # Force PyTorch backend
```

### 1.3 2D and 3D Literals

```simple
# ============================================
# 2D Matrix (nested array)
# ============================================
val mat = [
    [1, 2, 3],
    [4, 5, 6]
]_f64                               # 2x3 matrix, f64

val mat_gpu = [
    [1, 2, 3],
    [4, 5, 6]
]_f32_cuda                          # 2x3 matrix on CUDA

# ============================================
# 3D Tensor (deeply nested)
# ============================================
val tensor = [
    [[1, 2], [3, 4]],
    [[5, 6], [7, 8]]
]_f32_gpu                           # 2x2x2 tensor on GPU

# ============================================
# Trainable parameters
# ============================================
val W = [
    [0.1, 0.2, 0.3],
    [0.4, 0.5, 0.6]
]_f32_tr_cuda                       # Trainable 2x3 weight matrix
```

---

## 2. Factory Functions with Suffix-Style Options

### 2.1 Unified Factory Syntax

```simple
# ============================================
# zeros - consistent across all backends
# ============================================
val a = zeros([3, 4])               # Default (from config)
val b = zeros([3, 4])_f64           # f64, default device
val c = zeros([3, 4])_gpu           # Default type, GPU
val d = zeros([3, 4])_f32_cuda      # f32 on CUDA
val e = zeros([3, 4])_f32_tr_cuda   # Trainable f32 on CUDA

# ============================================
# ones
# ============================================
val a = ones([100])                 # 1D
val b = ones([100, 100])_gpu        # 2D on GPU
val c = ones([64, 3, 224, 224])_f32_cuda  # Batch of images

# ============================================
# randn (normal distribution)
# ============================================
val a = randn([100])                # Default
val W = randn([784, 256])_f32_tr_cuda  # Trainable weight matrix
val b = randn([256])_f32_tr_cuda    # Trainable bias

# ============================================
# Special constructors
# ============================================
val I = eye(4)_f64                  # 4x4 identity
val r = arange(0, 100)_i64          # [0, 1, ..., 99]
val l = linspace(0, 1, 100)_f32     # 100 points in [0, 1]
```

---

## 3. Configuration System

### 3.1 Global Config

```simple
# ============================================
# dl_config - Deep Learning configuration
# ============================================
struct DLConfig:
    """Global configuration for tensor operations."""
    default_dtype: DType = DType::Float32
    default_device: Device = Device::CPU
    default_backend: Backend = Backend::PyTorch
    enable_autograd: bool = true
    enable_amp: bool = false          # Automatic mixed precision
    seed: i64? = None                 # Random seed

# Global config instance
var dl_config = DLConfig()

# ============================================
# Configuration API
# ============================================
fn set_default_dtype(dtype: DType):
    dl_config.default_dtype = dtype

fn set_default_device(device: Device):
    dl_config.default_device = device

fn use_gpu():
    """Set GPU as default device."""
    dl_config.default_device = Device::CUDA(0)

fn use_cpu():
    """Set CPU as default device."""
    dl_config.default_device = Device::CPU

fn set_seed(seed: i64):
    """Set random seed for reproducibility."""
    dl_config.seed = Some(seed)
    native_set_seed(seed)
    torch_manual_seed(seed)
    cuda_manual_seed_all(seed)
```

### 3.2 Configuration Presets

```simple
# ============================================
# Presets for common scenarios
# ============================================
fn config_training():
    """Configure for GPU training."""
    dl_config = DLConfig(
        default_dtype: DType::Float32,
        default_device: Device::CUDA(0),
        default_backend: Backend::PyTorch,
        enable_autograd: true
    )

fn config_inference():
    """Configure for fast inference."""
    dl_config = DLConfig(
        default_dtype: DType::Float32,
        default_device: Device::CUDA(0),
        default_backend: Backend::PyTorch,
        enable_autograd: false
    )

fn config_development():
    """Configure for local development (CPU)."""
    dl_config = DLConfig(
        default_dtype: DType::Float64,
        default_device: Device::CPU,
        default_backend: Backend::Native,
        enable_autograd: false
    )

fn config_mixed_precision():
    """Configure for mixed precision training."""
    dl_config = DLConfig(
        default_dtype: DType::Float16,
        default_device: Device::CUDA(0),
        default_backend: Backend::PyTorch,
        enable_autograd: true,
        enable_amp: true
    )
```

### 3.3 Context-Based Config

```simple
# ============================================
# Temporary config changes
# ============================================
with config(device: cuda(1), dtype: f16):
    # All tensors created here use CUDA:1 and f16
    val a = zeros([100, 100])       # f16 on CUDA:1
    val b = randn([100, 100])       # f16 on CUDA:1

# Back to default config here
val c = zeros([100, 100])           # Uses global default
```

---

## 4. Unified Operations

### 4.1 Arithmetic Operations (All Backends)

```simple
# ============================================
# Same syntax for all backends
# ============================================
val a = randn([100, 100])_f32_gpu
val b = randn([100, 100])_f32_gpu

# Element-wise operations
val c = a + b                       # Add
val d = a - b                       # Subtract
val e = a * b                       # Multiply (element-wise)
val f = a / b                       # Divide
val g = a ** 2                      # Power

# Matrix operations
val h = a @ b                       # Matrix multiply
val i = a.T                         # Transpose
val j = a.T @ b                     # A^T * B

# Reductions
val sum = a.sum()                   # Sum all
val mean = a.mean()                 # Mean all
val row_sum = a.sum(axis: 0)        # Sum along axis
```

### 4.2 Backend-Agnostic Math Block

```simple
# ============================================
# m{} block works with any backend
# ============================================
val A = randn([100, 100])_f32_gpu
val x = randn([100])_f32_gpu
val b = randn([100])_f32_gpu

# Math block auto-dispatches to correct backend
val y = m{
    A @ x + b
}

# Complex expression
val loss = m{
    ((A @ x + b) - target)^2.mean()
}

# With trainable parameters
val W = randn([784, 256])_f32_tr_cuda
val result = m{
    relu(W @ input + bias)
}
result.backward()  # Works because W is trainable
```

---

## 5. Type Coercion Rules

### 5.1 Automatic Type Promotion

```simple
# ============================================
# Type promotion rules (consistent across backends)
# ============================================
val a = [1, 2, 3]_i32
val b = [1.0, 2.0, 3.0]_f32

# i32 + f32 -> f32
val c = a + b                       # Result is f32

# f32 + f64 -> f64
val d = [1.0]_f32
val e = [2.0]_f64
val f = d + e                       # Result is f64

# CPU + GPU -> Error (explicit transfer required)
val cpu = [1, 2, 3]_f32_cpu
val gpu = [1, 2, 3]_f32_gpu
# val bad = cpu + gpu               # Error!
val ok = cpu.to_gpu() + gpu         # OK
```

### 5.2 Device Transfer

```simple
# ============================================
# Explicit device transfer
# ============================================
val cpu_arr = [1, 2, 3, 4]_f32_cpu
val gpu_arr = cpu_arr.to_gpu()      # Transfer to GPU
val back = gpu_arr.to_cpu()         # Transfer back

# Shorthand
val gpu_arr = cpu_arr.cuda()        # Same as to_gpu()
val cpu_arr = gpu_arr.cpu()         # Same as to_cpu()

# Specific device
val cuda1 = cpu_arr.to(cuda(1))     # To CUDA:1
```

---

## 6. Complete Interface Comparison

### 6.1 Initialization

| Operation | Native | GPU | Torch | Unified |
|-----------|--------|-----|-------|---------|
| **Zeros 1D** | `[0.0; n]` | `gpu_zeros([n])` | `torch.zeros([n])` | `zeros([n])` |
| **Zeros 1D f64** | `[0.0f64; n]` | `gpu_zeros([n], f64)` | `torch.zeros([n], dtype=f64)` | `zeros([n])_f64` |
| **Zeros 1D GPU** | N/A | `gpu_zeros([n])` | `torch.zeros([n], device=cuda)` | `zeros([n])_gpu` |
| **Zeros 2D** | `[[0.0; n]; m]` | `gpu_zeros([m,n])` | `torch.zeros([m,n])` | `zeros([m,n])` |
| **Random** | manual | `gpu_randn([n])` | `torch.randn([n])` | `randn([n])` |
| **Trainable** | N/A | N/A | `torch.randn([n], requires_grad=True)` | `randn([n])_tr` |
| **From literal** | `[1,2,3]` | `gpu_from([1,2,3])` | `torch.tensor([1,2,3])` | `[1,2,3]_f32` |
| **From literal GPU** | N/A | `gpu_from([1,2,3])` | `torch.tensor([1,2,3], device=cuda)` | `[1,2,3]_f32_gpu` |

### 6.2 Operations

| Operation | Native | GPU | Torch | Unified |
|-----------|--------|-----|-------|---------|
| **Add** | `a + b` | `gpu_add(a, b)` | `a + b` | `a + b` |
| **Matmul** | manual | `gpu_matmul(a, b)` | `a @ b` | `a @ b` |
| **Transpose** | manual | `gpu_transpose(a)` | `a.T` | `a.T` |
| **Sum** | `a.sum()` | `gpu_sum(a)` | `a.sum()` | `a.sum()` |
| **Mean** | `a.mean()` | `gpu_mean(a)` | `a.mean()` | `a.mean()` |
| **Reshape** | manual | `gpu_reshape(a, s)` | `a.reshape(s)` | `a.reshape(s)` |
| **To GPU** | N/A | N/A | `a.cuda()` | `a.cuda()` |
| **To CPU** | identity | `a.to_cpu()` | `a.cpu()` | `a.cpu()` |
| **Backward** | N/A | N/A | `loss.backward()` | `loss.backward()` |

---

## 7. Suffix Grammar

### 7.1 Formal Grammar

```bnf
array_literal   := '[' elements ']' suffix?
suffix          := '_' suffix_part ('_' suffix_part)*
suffix_part     := dtype | device | modifier

dtype           := 'f16' | 'f32' | 'f64' | 'bf16'
                 | 'i8' | 'i16' | 'i32' | 'i64'
                 | 'u8' | 'u16' | 'u32' | 'u64'
                 | 'bool' | 'complex64' | 'complex128'

device          := 'cpu' | 'gpu' | 'cuda' | 'cuda' digit+
                 | 'vulkan' | 'metal' | 'native'

modifier        := 'tr'                   (* trainable/requires_grad *)
                 | 'pin'                  (* pinned memory *)
                 | 'torch'                (* force PyTorch backend *)
                 | 'native'               (* force native backend *)
```

### 7.2 Suffix Order

Suffixes can appear in any order, but recommended order is:

```
[data]_<dtype>_<modifier>_<device>
```

Examples:
```simple
[1, 2, 3]_f32              # dtype only
[1, 2, 3]_gpu              # device only
[1, 2, 3]_f32_gpu          # dtype + device
[1, 2, 3]_f32_tr           # dtype + trainable
[1, 2, 3]_f32_tr_cuda      # dtype + trainable + device
[1, 2, 3]_f32_tr_pin_cuda  # dtype + trainable + pinned + device
```

---

## 8. Implementation Strategy

### 8.1 Lexer Changes

```simple
# In lexer.spl - detect array suffix
fn scan_array_suffix() -> Option<ArraySuffix>:
    if not peek('_'):
        return None

    var dtype: DType? = None
    var device: Device? = None
    var trainable = false
    var pinned = false
    var backend: Backend? = None

    while peek('_'):
        advance()  # consume '_'
        val part = scan_identifier()

        match part:
            # DType
            case "f16": dtype = Some(DType::Float16)
            case "f32": dtype = Some(DType::Float32)
            case "f64": dtype = Some(DType::Float64)
            case "bf16": dtype = Some(DType::BFloat16)
            case "i32": dtype = Some(DType::Int32)
            case "i64": dtype = Some(DType::Int64)

            # Device
            case "cpu": device = Some(Device::CPU)
            case "gpu": device = Some(Device::CUDA(0))
            case "cuda": device = Some(Device::CUDA(0))
            case s if s.starts_with("cuda"):
                val id = s[4:].parse_int() ?? 0
                device = Some(Device::CUDA(id))

            # Modifiers
            case "tr": trainable = true
            case "pin": pinned = true
            case "native": backend = Some(Backend::Native)
            case "torch": backend = Some(Backend::PyTorch)

    Some(ArraySuffix(dtype, device, trainable, pinned, backend))
```

### 8.2 Type Resolution

```simple
# Resolve array literal type based on suffix and config
fn resolve_array_type(literal: ArrayLiteral, suffix: ArraySuffix?) -> TensorType:
    val dtype = suffix?.dtype ?? dl_config.default_dtype
    val device = suffix?.device ?? dl_config.default_device
    val trainable = suffix?.trainable ?? false
    val backend = suffix?.backend ?? select_backend(device, trainable)

    TensorType(
        element_type: dtype,
        shape: infer_shape(literal),
        device: device,
        requires_grad: trainable,
        backend: backend
    )
```

---

## 9. Full Example

### 9.1 Training Script with Unified Interface

```simple
import tensor.*

# ============================================
# Configuration
# ============================================
config_training()                    # Set GPU + autograd defaults
set_seed(42)                         # Reproducibility

# ============================================
# Model Parameters (using suffix notation)
# ============================================
val W1 = randn([784, 256])_f32_tr_cuda
val b1 = zeros([256])_f32_tr_cuda
val W2 = randn([256, 10])_f32_tr_cuda
val b2 = zeros([10])_f32_tr_cuda

# ============================================
# Forward Pass (m{} block, backend-agnostic)
# ============================================
fn forward(x: Tensor) -> Tensor:
    m{
        h = relu(W1 @ x + b1)
        W2 @ h + b2
    }

# ============================================
# Loss Function
# ============================================
fn compute_loss(logits: Tensor, targets: Tensor) -> Tensor:
    m{ cross_entropy(logits, targets) }

# ============================================
# Training Loop
# ============================================
val optimizer = Adam([W1, b1, W2, b2], lr: 0.001)

for epoch in 0..10:
    for (x_batch, y_batch) in train_loader:
        # Data already on GPU due to config
        optimizer.zero_grad()

        val logits = forward(x_batch)
        val loss = compute_loss(logits, y_batch)

        loss.backward()
        optimizer.step()

    # Validation
    with no_grad():
        val val_loss = evaluate(val_loader)
        print "Epoch {epoch}: loss = {val_loss:.4f}"
```

### 9.2 Quick Prototyping (CPU, No GPU)

```simple
import tensor.*

config_development()                 # CPU + native backend

# Small arrays, fast (no FFI overhead)
val A = [
    [1.0, 2.0],
    [3.0, 4.0]
]_f64                                # Native 2x2 matrix

val B = [
    [5.0, 6.0],
    [7.0, 8.0]
]_f64

val C = m{ A @ B }                   # Matrix multiply
print C                              # [[19, 22], [43, 50]]
```

---

## 10. Summary: Suffix Reference

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_f16` | Float16 | `[1,2,3]_f16` |
| `_f32` | Float32 | `[1,2,3]_f32` |
| `_f64` | Float64 | `[1,2,3]_f64` |
| `_bf16` | BFloat16 | `[1,2,3]_bf16` |
| `_i32` | Int32 | `[1,2,3]_i32` |
| `_i64` | Int64 | `[1,2,3]_i64` |
| `_cpu` | CPU device | `[1,2,3]_cpu` |
| `_gpu` | Default GPU | `[1,2,3]_gpu` |
| `_cuda` | CUDA GPU 0 | `[1,2,3]_cuda` |
| `_cuda0` | CUDA GPU 0 | `[1,2,3]_cuda0` |
| `_cuda1` | CUDA GPU 1 | `[1,2,3]_cuda1` |
| `_tr` | Trainable (requires_grad) | `[1,2,3]_tr` |
| `_pin` | Pinned memory | `[1,2,3]_pin` |
| `_native` | Force native backend | `[1,2,3]_native` |
| `_torch` | Force PyTorch backend | `[1,2,3]_torch` |

### Combined Examples

```simple
[1, 2, 3]_f32_gpu                   # f32 on default GPU
[1, 2, 3]_f32_tr_cuda               # Trainable f32 on CUDA
[1, 2, 3]_f16_tr_cuda0              # Trainable f16 on CUDA:0
zeros([100, 100])_f32_tr_cuda       # Trainable zeros on CUDA
randn([784, 256])_f32_tr_cuda       # Trainable random weights
```

---

## 11. References

- [Rust Literal Suffixes](https://doc.rust-lang.org/rust-by-example/types/literals.html)
- [Swift ExpressibleByArrayLiteral](https://developer.apple.com/documentation/swift/expressiblebyarrayliteral)
- [Julia CuArray](https://cuda.juliagpu.org/stable/usage/array/)
- [PyTorch TensorOptions](https://docs.pytorch.org/cppdocs/notes/tensor_creation.html)
- [NumPy Array Protocol](https://numpy.org/doc/stable/user/basics.dispatch.html)
