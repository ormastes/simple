# Unified Tensor Interface - Final Design

**Date:** 2026-01-26
**Status:** Final Research
**Supersedes:** `unified_tensor_creation.md`, `tensor_init_comparison.md`, `unified_tensor_interface.md`, `math_torch_seamless_integration.md`

---

## 1. Design Goals

| Goal | Description |
|------|-------------|
| **Unified syntax** | Same code works on CPU, GPU, PyTorch |
| **Suffix notation** | `]f32_gpu` and `]_f32_gpu` both valid |
| **Config defaults** | DL config sets default dtype/device |
| **Block syntax** | `m{}`, `loss{}`, `nograd{}` for context |
| **Seamless autograd** | Trainable suffix `_tr` enables gradients |

---

## 2. Suffix Notation

### 2.1 Both Styles Supported

```simple
# ============================================
# SCALARS - Both styles equivalent
# ============================================
val a = 0f32                        # Attached style
val a = 0_f32                       # Underscore style

val b = 3.14f64                     # Attached
val b = 3.14_f64                    # Underscore

# ============================================
# ARRAYS - Both styles equivalent
# ============================================
val arr = [1, 2, 3]f32              # Attached: ]f32
val arr = [1, 2, 3]_f32             # Underscore: ]_f32

val arr = [1, 2, 3]f32_gpu          # Mixed: ]f32_gpu
val arr = [1, 2, 3]_f32_gpu         # All underscore: ]_f32_gpu

# ============================================
# NESTED ARRAYS - Same rules
# ============================================
val mat = [[1, 2], [3, 4]]f32       # 2D, attached
val mat = [[1, 2], [3, 4]]_f32_gpu  # 2D, underscore, GPU
```

### 2.2 Suffix Reference

| Suffix | Meaning | Scalar | Array |
|--------|---------|--------|-------|
| **DType** | | | |
| `f16` | Float16 | `0f16` | `[1,2]f16` |
| `f32` | Float32 | `0f32` | `[1,2]f32` |
| `f64` | Float64 | `0f64` | `[1,2]f64` |
| `bf16` | BFloat16 | `0bf16` | `[1,2]bf16` |
| `i32` | Int32 | `0i32` | `[1,2]i32` |
| `i64` | Int64 | `0i64` | `[1,2]i64` |
| **Device** | | | |
| `cpu` | CPU | - | `[1,2]_cpu` |
| `gpu` | Default GPU | - | `[1,2]_gpu` |
| `cuda` | CUDA:0 | - | `[1,2]_cuda` |
| `cuda0` | CUDA:0 | - | `[1,2]_cuda0` |
| `cuda1` | CUDA:1 | - | `[1,2]_cuda1` |
| **Modifier** | | | |
| `tr` | Trainable | - | `[1,2]_tr` |
| `pin` | Pinned memory | - | `[1,2]_pin` |
| **Backend** | | | |
| `native` | Native backend | - | `[1,2]_native` |
| `torch` | PyTorch backend | - | `[1,2]_torch` |

### 2.3 Combined Suffix Examples

```simple
# Single suffix
[1, 2, 3]f32                        # Just dtype
[1, 2, 3]_gpu                       # Just device

# Two suffixes
[1, 2, 3]f32_gpu                    # dtype + device
[1, 2, 3]_f32_gpu                   # Same (underscore style)
[1, 2, 3]f32_tr                     # dtype + trainable

# Three suffixes
[1, 2, 3]f32_tr_gpu                 # dtype + trainable + device
[1, 2, 3]_f32_tr_cuda               # All underscore style

# Four suffixes
[1, 2, 3]f32_tr_pin_cuda            # dtype + trainable + pinned + device
```

---

## 3. Factory Functions

### 3.1 Unified Factories with Suffix

```simple
# ============================================
# zeros - All forms equivalent
# ============================================
zeros([3, 4])                       # Default (from config)
zeros([3, 4])f32                    # f32, default device
zeros([3, 4])_f32                   # Same, underscore
zeros([3, 4])f32_gpu                # f32 on GPU
zeros([3, 4])_f32_gpu               # Same, underscore
zeros([3, 4])f32_tr_cuda            # Trainable f32 on CUDA

# ============================================
# ones
# ============================================
ones([100])                         # 1D
ones([100, 100])_gpu                # 2D on GPU
ones([64, 3, 224, 224])f32_cuda     # Batch of images

# ============================================
# randn (normal distribution)
# ============================================
randn([100])                        # Default
randn([784, 256])f32_tr_cuda        # Trainable weight matrix

# ============================================
# Other factories
# ============================================
eye(4)f64                           # 4x4 identity, f64
arange(0, 100)i64                   # [0..99], i64
linspace(0, 1, 100)f32              # 100 points, f32
full([3, 4], 3.14)f64               # Fill with value
rand([10, 10])f32_gpu               # Uniform random on GPU
```

---

## 4. Configuration System

### 4.1 DL Config Structure

```simple
struct DLConfig:
    """Deep learning configuration."""
    default_dtype: DType = DType::Float32
    default_device: Device = Device::CPU
    default_backend: Backend = Backend::PyTorch
    autograd_enabled: bool = true
    amp_enabled: bool = false         # Automatic mixed precision
    seed: i64? = nil

# Global instance
var dl = DLConfig()
```

### 4.2 Config API

```simple
# ============================================
# Setters
# ============================================
dl.dtype(f32)                       # Set default dtype
dl.device(cuda(0))                  # Set default device
dl.backend(torch)                   # Set default backend
dl.seed(42)                         # Set random seed

# ============================================
# Shorthand functions
# ============================================
use_gpu()                           # dl.device(cuda(0))
use_cpu()                           # dl.device(cpu)
use_f16()                           # dl.dtype(f16)
use_f32()                           # dl.dtype(f32)
use_f64()                           # dl.dtype(f64)

# ============================================
# Presets
# ============================================
config_training()                   # GPU + f32 + autograd
config_inference()                  # GPU + f32 + no autograd
config_development()                # CPU + f64 + native
config_mixed_precision()            # GPU + f16 + AMP
```

### 4.3 Config Context

```simple
# Temporary config change
with config(device: cuda(1), dtype: f16):
    val a = zeros([100])            # f16 on CUDA:1
    val b = randn([100])            # f16 on CUDA:1
# Back to default
```

---

## 5. Block Syntax

### 5.1 Math Block `m{}`

Math block enables mathematical notation:
- `^` for power (instead of `**`)
- `'` for transpose (postfix)
- Implicit multiplication (`2x` → `2*x`)

```simple
# ============================================
# Power operator (^ only in m{})
# ============================================
val y = m{ x^2 + 2*x + 1 }          # Quadratic
val d = m{ sqrt(x^2 + y^2) }        # Distance

# Outside m{}, use **
val y = x ** 2 + 2 * x + 1

# ============================================
# Transpose (postfix ')
# ============================================
val y = m{ A' @ x }                 # A^T * x
val z = m{ (A' @ A)^-1 @ A' @ b }   # Normal equations

# Outside m{}, use .T
val y = A.T @ x

# ============================================
# Implicit multiplication
# ============================================
val y = m{ 2x + 3 }                 # 2*x + 3
val area = m{ pi * r^2 }            # π * r²
val quad = m{ ax^2 + bx + c }       # a*x² + b*x + c

# ============================================
# Matrix operations
# ============================================
val y = m{
    h = relu(W1 @ x + b1)
    W2 @ h + b2
}
```

### 5.2 Loss Block `loss{}`

Loss block marks differentiable computation with automatic backward:

```simple
# ============================================
# Basic loss computation
# ============================================
val total_loss = loss{
    y = model(x)
    cross_entropy(y, target)
}
# Gradients automatically computed

# ============================================
# Equivalent to
# ============================================
val total_loss = m{
    y = model(x)
    cross_entropy(y, target)
}
total_loss.backward()

# ============================================
# Complex loss
# ============================================
val total_loss = loss{
    pred = model(x)
    ce = cross_entropy(pred, target)
    reg = 0.01 * (W1.norm()^2 + W2.norm()^2)
    ce + reg
}
# Backward called automatically
```

### 5.3 No-Grad Block `nograd{}`

No-grad block disables gradient tracking (faster, less memory):

```simple
# ============================================
# Inference (no gradients)
# ============================================
val predictions = nograd{
    model(test_data)
}

# ============================================
# Validation loop
# ============================================
nograd{
    var total = 0f32
    for (x, y) in val_loader:
        val pred = model(x)
        total += accuracy(pred, y)
    print "Accuracy: {total / val_loader.len()}"
}

# ============================================
# Equivalent to
# ============================================
with no_grad():
    val predictions = model(test_data)
```

### 5.4 Block Grammar

```bnf
math_block    := 'm' '{' expr '}'
loss_block    := 'loss' '{' statements expr '}'
nograd_block  := 'nograd' '{' statements '}'

# Inside m{} and loss{}:
#   - ^ is power operator
#   - ' is postfix transpose
#   - Implicit multiplication enabled
```

---

## 6. Unified Operations

### 6.1 Operations Work Across All Backends

```simple
# Same code, any backend
val a = randn([100, 100])f32_gpu
val b = randn([100, 100])f32_gpu

# Arithmetic
val c = a + b                       # Element-wise add
val d = a - b                       # Element-wise sub
val e = a * b                       # Element-wise mul
val f = a / b                       # Element-wise div

# Matrix operations
val g = a @ b                       # Matrix multiply
val h = a.T                         # Transpose
val i = a.T @ b                     # A^T * B

# Reductions
val s = a.sum()                     # Sum all
val m = a.mean()                    # Mean all
val rs = a.sum(axis: 0)             # Row sums

# In-place (with _)
a += b                              # In-place add
a *= 2.0                            # In-place scale
```

### 6.2 Device Transfer

```simple
val cpu_arr = [1, 2, 3]f32_cpu
val gpu_arr = cpu_arr.gpu()         # To GPU
val back = gpu_arr.cpu()            # To CPU

# Specific device
val cuda1 = cpu_arr.to(cuda(1))     # To CUDA:1

# Check device
if arr.is_gpu():
    print "On GPU"
```

---

## 7. Complete Examples

### 7.1 Training Script

```simple
import tensor.*

# ============================================
# Configuration
# ============================================
config_training()                    # GPU + f32 + autograd
dl.seed(42)

# ============================================
# Model Parameters
# ============================================
val W1 = randn([784, 256])f32_tr_cuda
val b1 = zeros([256])f32_tr_cuda
val W2 = randn([256, 10])f32_tr_cuda
val b2 = zeros([10])f32_tr_cuda

# ============================================
# Forward (math block)
# ============================================
fn forward(x):
    m{
        h = relu(W1 @ x + b1)
        W2 @ h + b2
    }

# ============================================
# Training Loop
# ============================================
val optimizer = Adam([W1, b1, W2, b2], lr: 0.001)

for epoch in 0..10:
    for (x, y) in train_loader:
        optimizer.zero_grad()

        # Loss block (auto backward)
        val l = loss{
            pred = forward(x)
            cross_entropy(pred, y)
        }

        optimizer.step()

    # Validation (no grad)
    nograd{
        val acc = evaluate(val_loader)
        print "Epoch {epoch}: acc = {acc:.2%}"
    }
```

### 7.2 Quick Prototyping (CPU)

```simple
import tensor.*

config_development()                 # CPU + native

# Small matrices, fast
val A = [[1, 2], [3, 4]]f64
val B = [[5, 6], [7, 8]]f64

val C = m{ A @ B }
print C                              # [[19, 22], [43, 50]]

val D = m{ A' @ B }                  # Transpose
print D                              # [[26, 30], [38, 44]]
```

### 7.3 Mixed Precision Training

```simple
import tensor.*

config_mixed_precision()             # GPU + f16 + AMP

val W = randn([1024, 1024])f16_tr_cuda

for batch in data:
    val l = loss{
        y = m{ W @ batch.x }
        mse(y, batch.y)
    }
    optimizer.step()
```

---

## 8. Type Coercion Rules

### 8.1 Automatic Promotion

```simple
# Type promotion (same as NumPy/PyTorch)
f16 + f32 → f32
f32 + f64 → f64
i32 + f32 → f32
i64 + f64 → f64
```

### 8.2 Device Rules

```simple
# Same device required for operations
cpu + cpu → cpu
gpu + gpu → gpu
cpu + gpu → ERROR (explicit transfer needed)

# Transfer explicitly
val result = a.gpu() + b            # a to GPU, then add
```

---

## 9. Grammar Summary

### 9.1 Suffix Grammar

```bnf
literal         := scalar_literal | array_literal
scalar_literal  := NUMBER suffix?
array_literal   := '[' elements ']' suffix?

suffix          := attached_suffix | underscore_suffix
attached_suffix := DTYPE                          # ]f32
underscore_suffix := ('_' suffix_part)+           # ]_f32_gpu

suffix_part     := DTYPE | DEVICE | MODIFIER | BACKEND

DTYPE           := 'f16' | 'f32' | 'f64' | 'bf16'
                 | 'i8' | 'i16' | 'i32' | 'i64'
                 | 'u8' | 'u16' | 'u32' | 'u64'

DEVICE          := 'cpu' | 'gpu' | 'cuda' DIGIT*

MODIFIER        := 'tr' | 'pin'

BACKEND         := 'native' | 'torch'
```

### 9.2 Block Grammar

```bnf
block           := math_block | loss_block | nograd_block

math_block      := 'm' '{' math_expr '}'
loss_block      := 'loss' '{' stmt* math_expr '}'
nograd_block    := 'nograd' '{' stmt* '}'

# Inside math_block and loss_block:
math_expr       := ... | power_expr | transpose_expr | implicit_mul
power_expr      := expr '^' expr
transpose_expr  := expr "'"
implicit_mul    := NUMBER IDENT | NUMBER '(' | ')' IDENT | ')' '('
```

---

## 10. Implementation Checklist

### Phase 1: Suffix Parsing
- [ ] Lexer: `]f32` attached suffix
- [ ] Lexer: `]_f32` underscore suffix
- [ ] Lexer: Multi-part `]f32_tr_gpu`
- [ ] Parser: Suffix on array literals
- [ ] Parser: Suffix on factory calls

### Phase 2: Config System
- [ ] DLConfig struct
- [ ] Global dl instance
- [ ] Preset functions
- [ ] Context manager

### Phase 3: Block Syntax
- [ ] `m{}` math block (exists)
- [ ] `loss{}` block with auto-backward
- [ ] `nograd{}` block

### Phase 4: Backend Dispatch
- [ ] Native backend implementation
- [ ] PyTorch backend (exists)
- [ ] GPU backend (CUDA FFI)
- [ ] Auto-selection logic

### Phase 5: Operations
- [ ] Unified arithmetic
- [ ] Unified reductions
- [ ] Device transfer methods
- [ ] Type coercion

---

## 11. References

- [Rust Literal Suffixes](https://doc.rust-lang.org/rust-by-example/types/literals.html)
- [PyTorch TensorOptions](https://docs.pytorch.org/cppdocs/notes/tensor_creation.html)
- [JAX Device Management](https://apxml.com/courses/getting-started-with-jax/chapter-1-introduction-to-jax/jax-device-management)
- [Julia CuArray](https://cuda.juliagpu.org/stable/usage/array/)
- [Swift ExpressibleByArrayLiteral](https://developer.apple.com/documentation/swift/expressiblebyarrayliteral)
