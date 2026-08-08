# Tensor Initialization Comparison

**Date:** 2026-01-26
**Status:** Research
**Related:** `unified_tensor_creation.md`

## Overview

Comparison of variable initialization across:
- **Dimensions**: Array (1D), Matrix (2D), Tensor (3D+)
- **Backends**: CPU Native, CUDA GPU, PyTorch Tensor

---

## 1. Dimension Terminology

| Term | Dimensions | Shape Example | Use Case |
|------|------------|---------------|----------|
| **Scalar** | 0D | `[]` | Single value |
| **Array/Vector** | 1D | `[n]` | Lists, sequences |
| **Matrix** | 2D | `[m, n]` | Tables, images (grayscale) |
| **Tensor** | 3D+ | `[d, h, w]` | Images (RGB), batches, volumes |

---

## 2. Initialization Comparison Table

### 2.1 Zeros Initialization

| Type | CPU Native | CUDA GPU | PyTorch Tensor |
|------|------------|----------|----------------|
| **1D Array** `[n]` | `[0.0; n]` | `gpu_zeros([n])` | `torch.zeros([n])` |
| **2D Matrix** `[m,n]` | `[[0.0; n]; m]` | `gpu_zeros([m,n])` | `torch.zeros([m,n])` |
| **3D Tensor** `[d,h,w]` | `[[[0.0; w]; h]; d]` | `gpu_zeros([d,h,w])` | `torch.zeros([d,h,w])` |

### 2.2 Random Initialization

| Type | CPU Native | CUDA GPU | PyTorch Tensor |
|------|------------|----------|----------------|
| **1D Array** | `rand_array(n)` | `gpu_randn([n])` | `torch.randn([n])` |
| **2D Matrix** | `rand_matrix(m,n)` | `gpu_randn([m,n])` | `torch.randn([m,n])` |
| **3D Tensor** | `rand_tensor(d,h,w)` | `gpu_randn([d,h,w])` | `torch.randn([d,h,w])` |

---

## 3. Code Examples by Backend

### 3.1 CPU Native (Pure Simple, No FFI)

```simple
# ============================================
# 1D Array (Vector)
# ============================================
val arr1: [f64; 5] = [0.0; 5]                    # Zeros, compile-time size
val arr2: [f64] = [0.0, 0.0, 0.0, 0.0, 0.0]     # Zeros, literal
val arr3 = List::filled(5, 0.0)                  # Zeros, runtime size
val arr4 = Array::filled(0.0)                    # Generic, fixed size

# ============================================
# 2D Matrix
# ============================================
val mat1: [[f64; 4]; 3] = [[0.0; 4]; 3]         # 3x4 zeros, nested
val mat2 = Matrix::zeros(3, 4)                   # Factory method
val mat3 = [
    [1.0, 2.0, 3.0],
    [4.0, 5.0, 6.0]
]                                                # Literal

# ============================================
# 3D Tensor
# ============================================
val t1: [[[f64; 4]; 3]; 2] = [[[0.0; 4]; 3]; 2] # 2x3x4, deeply nested
val t2 = NativeTensor::zeros([2, 3, 4])          # Factory method

# Random initialization (CPU)
val rand_arr = (0..100).map(\_ -> random()).collect()
val rand_mat = Matrix::random(3, 4)
```

**Characteristics:**
- Fast for small sizes (no FFI overhead)
- Compile-time size checking possible
- No autograd support
- Limited operations (manual implementation)

---

### 3.2 CUDA GPU (via FFI)

```simple
import gpu.*

# ============================================
# 1D Array on GPU
# ============================================
val arr_gpu = gpu_zeros([1000], device: cuda(0))
val arr_rand = gpu_randn([1000], device: cuda(0))

# ============================================
# 2D Matrix on GPU
# ============================================
val mat_gpu = gpu_zeros([1000, 1000], device: cuda(0))
val mat_rand = gpu_randn([1000, 1000], device: cuda(0))

# ============================================
# 3D Tensor on GPU
# ============================================
val t_gpu = gpu_zeros([64, 224, 224], device: cuda(0))  # Batch of images

# Transfer from CPU to GPU
val cpu_data = [[1.0, 2.0], [3.0, 4.0]]
val gpu_data = gpu_from_data(cpu_data, device: cuda(0))

# Transfer back to CPU
val result_cpu = gpu_data.to_cpu()
```

**Characteristics:**
- Fast for large computations (parallel)
- Requires explicit device management
- Memory transfer overhead (CPU ↔ GPU)
- No autograd (raw compute only)

---

### 3.3 PyTorch Tensor (Full Featured)

```simple
import ml.torch as torch

# ============================================
# 1D Array (Tensor)
# ============================================
val arr = torch.zeros([100])                     # CPU, f32
val arr_f64 = torch.zeros([100], dtype: f64)    # CPU, f64
val arr_cuda = torch.zeros([100], device: cuda(0))  # GPU
val arr_grad = torch.zeros([100], requires_grad: true)  # With autograd

# ============================================
# 2D Matrix (Tensor)
# ============================================
val mat = torch.zeros([3, 4])                    # 3x4 matrix
val mat_cuda = torch.zeros([1000, 1000], device: cuda(0))
val mat_param = torch.randn([784, 256], requires_grad: true)  # Trainable

# ============================================
# 3D Tensor
# ============================================
val t = torch.zeros([2, 3, 4])                   # 2x3x4 tensor
val batch = torch.randn([64, 3, 224, 224])       # Batch of RGB images
val batch_cuda = torch.randn([64, 3, 224, 224], device: cuda(0))

# From data
val from_list = torch.from_data([[1.0, 2.0], [3.0, 4.0]])

# Random initialization
val randn = torch.randn([100, 100])              # Normal(0, 1)
val rand = torch.rand([100, 100])                # Uniform(0, 1)
val randint = torch.randint(0, 10, [100])        # Random integers

# Special matrices
val eye = torch.eye(4)                           # 4x4 identity
val ones = torch.ones([3, 4])
val full = torch.full([3, 4], 3.14)
val arange = torch.arange(0, 10, 1)              # [0, 1, ..., 9]
val linspace = torch.linspace(0.0, 1.0, 100)    # 100 points in [0, 1]
```

**Characteristics:**
- Unified API for all dimensions
- Automatic device placement
- Full autograd support
- Rich operations library
- Interop with Python ecosystem

---

## 4. Side-by-Side Initialization

### 4.1 Creating a 3x4 Matrix of Zeros

```simple
# CPU Native
val native_mat: [[f64; 4]; 3] = [[0.0; 4]; 3]

# GPU (CUDA)
val gpu_mat = gpu_zeros([3, 4], device: cuda(0))

# PyTorch CPU
val torch_cpu = torch.zeros([3, 4])

# PyTorch CUDA
val torch_cuda = torch.zeros([3, 4], device: cuda(0))
```

### 4.2 Creating a Random 100x100 Matrix

```simple
# CPU Native (manual)
val native_rand = Matrix::filled_with(100, 100, \_, _ -> random_normal())

# GPU (CUDA)
val gpu_rand = gpu_randn([100, 100], device: cuda(0))

# PyTorch CPU
val torch_cpu = torch.randn([100, 100])

# PyTorch CUDA
val torch_cuda = torch.randn([100, 100], device: cuda(0))
```

### 4.3 Creating Trainable Parameters

```simple
# CPU Native - NO AUTOGRAD SUPPORT
# Must implement gradients manually

# GPU (CUDA) - NO AUTOGRAD SUPPORT
# Must implement gradients manually via compute shaders

# PyTorch - FULL AUTOGRAD
val W = torch.randn([784, 256], requires_grad: true)
val b = torch.zeros([256], requires_grad: true)

# Usage
val y = W @ x + b
val loss = (y - target).pow(2).mean()
loss.backward()  # Computes W.grad and b.grad automatically
```

---

## 5. Proposed Unified API

### 5.1 Consistent Initialization Syntax

```simple
import tensor.*

# The SAME syntax works for all backends
# Backend selected by options

# 1D Array
val arr_cpu = zeros([100])                       # CPU native
val arr_gpu = zeros([100], cuda())               # CUDA
val arr_torch = zeros([100], torch())            # PyTorch

# 2D Matrix
val mat_cpu = zeros([100, 100])
val mat_gpu = zeros([100, 100], cuda())
val mat_torch = zeros([100, 100], torch().grad())  # With autograd

# 3D Tensor
val t_cpu = zeros([64, 28, 28])
val t_gpu = zeros([64, 28, 28], cuda())
val t_torch = zeros([64, 28, 28], torch())

# Random
val r_cpu = randn([100, 100])
val r_gpu = randn([100, 100], cuda())
val r_param = randn([784, 256], param())         # Trainable parameter
```

### 5.2 Type Aliases for Clarity

```simple
# Semantic type aliases
type Vector<T> = Tensor<T, 1>      # 1D
type Matrix<T> = Tensor<T, 2>      # 2D
type Tensor3D<T> = Tensor<T, 3>    # 3D
type Tensor4D<T> = Tensor<T, 4>    # 4D (batched images)

# Concrete shortcuts
type Vec = Vector<f64>
type Mat = Matrix<f64>
type Mat32 = Matrix<f32>

# Usage with explicit types
val v: Vec = zeros([100])
val m: Mat = randn([100, 100])
val batch: Tensor4D<f32> = zeros([64, 3, 224, 224], f32())
```

---

## 6. Feature Comparison Matrix

| Feature | CPU Native | CUDA GPU | PyTorch Tensor |
|---------|------------|----------|----------------|
| **Initialization** | | | |
| zeros | `[0.0; n]` | `gpu_zeros` | `torch.zeros` |
| ones | `[1.0; n]` | `gpu_ones` | `torch.ones` |
| random | Manual loop | `gpu_randn` | `torch.randn` |
| from data | Literal | `gpu_from_data` | `torch.from_data` |
| **Device** | | | |
| CPU | Default | N/A | `device: cpu()` |
| CUDA | N/A | `device: cuda(n)` | `device: cuda(n)` |
| Multi-GPU | N/A | Manual | Supported |
| **Types** | | | |
| f16 | No | Yes | Yes |
| f32 | Yes | Yes | Yes (default) |
| f64 | Yes (default) | Yes | Yes |
| bf16 | No | Yes (Ampere+) | Yes |
| **Autograd** | | | |
| requires_grad | No | No | Yes |
| backward() | No | No | Yes |
| grad access | No | No | `t.grad` |
| **Performance** | | | |
| Small arrays | Fastest | Overhead | FFI overhead |
| Large arrays | Slow | Fastest | Fast |
| Batch ops | Manual | Yes | Yes |
| **Memory** | | | |
| Pinned | N/A | Manual | `pin_memory=true` |
| Async transfer | N/A | Manual | `non_blocking=true` |

---

## 7. When to Use Each Backend

### Use CPU Native When:
- Small arrays (< 1000 elements)
- No GPU needed
- Maximum control over memory
- Compile-time size known
- No autograd needed

### Use CUDA GPU When:
- Large parallel computations
- Custom GPU kernels
- Maximum GPU performance
- No autograd needed
- Fine-grained memory control

### Use PyTorch Tensor When:
- Machine learning training/inference
- Need autograd (backpropagation)
- Interop with ML ecosystem
- Mixed CPU/GPU workflows
- Production deployment

---

## 8. Migration Patterns

### From Native to PyTorch

```simple
# Before (Native)
val mat: [[f64; 100]; 100] = [[0.0; 100]; 100]
# Manual operations...

# After (PyTorch)
val mat = torch.zeros([100, 100])
# Use torch operations...
```

### From CPU to CUDA

```simple
# Before (CPU)
val mat = torch.zeros([1000, 1000])

# After (CUDA) - just add device
val mat = torch.zeros([1000, 1000], device: cuda(0))

# Or transfer existing
val mat_gpu = mat.to(cuda(0))
```

### Adding Autograd

```simple
# Before (no grad)
val W = torch.randn([784, 256])

# After (with grad)
val W = torch.randn([784, 256], requires_grad: true)
# Or
val W = torch.randn([784, 256])
W.requires_grad_(true)
```

---

## 9. Summary Table

| Operation | CPU Native | CUDA | PyTorch CPU | PyTorch CUDA |
|-----------|------------|------|-------------|--------------|
| **Init zeros 1D** | `[0.0; n]` | `gpu_zeros([n])` | `zeros([n])` | `zeros([n], cuda())` |
| **Init zeros 2D** | `[[0.0; n]; m]` | `gpu_zeros([m,n])` | `zeros([m,n])` | `zeros([m,n], cuda())` |
| **Init zeros 3D** | Nested literal | `gpu_zeros([d,h,w])` | `zeros([d,h,w])` | `zeros([d,h,w], cuda())` |
| **Init random** | Manual | `gpu_randn(shape)` | `randn(shape)` | `randn(shape, cuda())` |
| **Init trainable** | N/A | N/A | `randn(shape, grad())` | `randn(shape, cuda().grad())` |
| **From data** | Literal | `gpu_from_data` | `from_data(data)` | `from_data(data).cuda()` |
| **Transfer** | N/A | `to_cpu()` | N/A | `to(device)` |

---

## 10. Recommended Unified Syntax

```simple
import tensor.*

# Unified factory - backend auto-selected
val a = zeros([3, 4])                    # CPU, f32, no grad
val b = zeros([3, 4], f64())             # CPU, f64, no grad
val c = zeros([3, 4], cuda())            # CUDA, f32, no grad
val d = zeros([3, 4], cuda().f64())      # CUDA, f64, no grad
val e = zeros([3, 4], param())           # CPU, f32, with grad
val f = zeros([3, 4], param().cuda())    # CUDA, f32, with grad

# Same pattern for all factories
val g = ones([3, 4], cuda())
val h = randn([100, 100], param().cuda())
val i = rand([10, 10])
val j = eye(4, cuda())
val k = arange(0, 100)
val l = linspace(0.0, 1.0, 100, f64())
```

This unified syntax handles:
- All dimensions (1D, 2D, 3D, ND)
- All backends (CPU, CUDA, native)
- All dtypes (f16, f32, f64, i32, i64)
- Autograd (requires_grad)
