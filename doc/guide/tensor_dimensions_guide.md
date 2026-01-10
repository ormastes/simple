# Tensor Dimension Inference - User Guide

**Feature ID:** #193
**Status:** Implementing
**Module:** `ml.torch.typed_tensor`

## Table of Contents

1. [Introduction](#introduction)
2. [Quick Start](#quick-start)
3. [Dimension Specifications](#dimension-specifications)
4. [Shape Inference Operations](#shape-inference-operations)
5. [Runtime Verification](#runtime-verification)
6. [Memory Estimation](#memory-estimation)
7. [Advanced Patterns](#advanced-patterns)
8. [Troubleshooting](#troubleshooting)

---

## Introduction

Tensor dimension inference provides compile-time tracking of N-dimensional tensor shapes with optional range constraints. This feature helps prevent runtime shape errors by catching dimension mismatches during type checking and providing runtime verification for dynamic dimensions.

### Key Benefits

- **Catch Errors Early**: Detect shape mismatches at compile time
- **Self-Documenting Code**: Dimension names make tensor purposes clear
- **Memory Planning**: Estimate memory usage before allocation
- **Formal Verification**: Generate Lean 4 proofs of correctness

### When to Use TypedTensor

Use `TypedTensor` when you need:
- Compile-time shape inference through operations
- Named dimensions for self-documenting code (e.g., "batch", "seq_len")
- Memory estimation from dimension bounds
- Runtime verification of dynamic dimensions

Use regular `Tensor` when:
- Shapes are fully dynamic
- Performance is critical (typed tensors have small overhead)
- Integration with existing PyTorch code is needed

---

## Quick Start

### Installation

TypedTensor is part of the Simple standard library:

```simple
import ml.torch.{TypedTensor, DimSpec}
import ml.torch.dtype.{DType}
```

### Your First Typed Tensor

```simple
# Create a tensor with exact dimensions
let t = TypedTensor.zeros([
    DimSpec.exact(64),    # Exactly 64 rows
    DimSpec.exact(128)    # Exactly 128 columns
])

print("Shape: {t.actual_shape()}")  # [64, 128]
print("Dimensions: {t.ndim()}")     # 2
```

### Matrix Multiplication with Inference

```simple
# Create input tensor [4, 8]
let a = TypedTensor.randn([
    DimSpec.exact(4),
    DimSpec.exact(8)
])

# Create weight tensor [8, 16]
let b = TypedTensor.randn([
    DimSpec.exact(8),
    DimSpec.exact(16)
])

# Matmul infers output shape [4, 16]
match a.matmul(b):
    case Ok(c):
        print("Output shape: {c.actual_shape()}")  # [4, 16]
    case Err(e):
        print("Shape error: {e}")
```

---

## Dimension Specifications

Dimensions can be specified in several ways to balance compile-time inference and runtime flexibility.

### Exact Dimensions

Fixed dimension known at compile time:

```simple
let t = TypedTensor.zeros([
    DimSpec.exact(64),
    DimSpec.exact(256)
])
# Shape is always [64, 256]
```

**Use when:**
- Dimension is fixed (e.g., image size, feature count)
- Want strictest type checking

### Named Dimensions

Dimension with a descriptive name:

```simple
let t = TypedTensor.randn([
    DimSpec.named("batch", 32),       # Sample value: 32
    DimSpec.named("features", 784)    # Sample value: 784
])
# Self-documenting: this is a batch of feature vectors
```

**Use when:**
- Want self-documenting code
- Dimension value may vary but has semantic meaning

### Ranged Dimensions

Named dimension with min/max constraints:

```simple
let t = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),  # Sample: 32, Range: [1, 64]
    DimSpec.exact(784)
])
# Batch can be 1-64, features always 784
```

**Use when:**
- Need runtime flexibility within bounds
- Want memory estimation (min/max memory usage)
- Training with variable batch sizes

### Dynamic Dimensions

Fully dynamic dimension (no compile-time constraint):

```simple
let t = TypedTensor.randn([
    DimSpec.dynamic(),    # No constraints
    DimSpec.exact(128)
])
# First dimension completely flexible
```

**Use when:**
- Shape truly unpredictable
- Interfacing with external code

### Comparison Table

| Type | Compile-Time | Runtime Check | Memory Estimation | Example |
|------|-------------|---------------|-------------------|---------|
| Exact | Fully known | Exact match | Exact | `DimSpec.exact(64)` |
| Named | Sample only | None | Sample-based | `DimSpec.named("batch", 32)` |
| Ranged | Sample + range | Range bounds | Min/max | `DimSpec.ranged("batch", 32, 1, 64)` |
| Dynamic | None | None | Unknown | `DimSpec.dynamic()` |

---

## Shape Inference Operations

TypedTensor supports shape inference for common tensor operations.

### Matrix Multiplication

Shape rule: `[M, K] @ [K, N] -> [M, N]`

```simple
let a = TypedTensor.randn([DimSpec.exact(4), DimSpec.exact(8)])   # [4, 8]
let b = TypedTensor.randn([DimSpec.exact(8), DimSpec.exact(16)])  # [8, 16]

match a.matmul(b):
    case Ok(c):
        # c has shape [4, 16]
        assert c.ndim() == 2
    case Err(ShapeError.MatmulShapeMismatch(left, right)):
        print("Incompatible shapes: {left} @ {right}")
```

### Broadcasting

Arithmetic operations broadcast following NumPy rules:

```simple
# [3, 4] + [1, 4] -> [3, 4]
let a = TypedTensor.randn([DimSpec.exact(3), DimSpec.exact(4)])
let b = TypedTensor.randn([DimSpec.exact(1), DimSpec.exact(4)])

let c = a.add(b)?
assert c.actual_shape() == [3, 4]
```

Supported operations: `add`, `sub`, `mul`, `div`

### Reshape

Element count must match:

```simple
# [4, 6] -> [2, 12] (both have 24 elements)
let t = TypedTensor.randn([DimSpec.exact(4), DimSpec.exact(6)])

match t.reshape([DimSpec.exact(2), DimSpec.exact(12)]):
    case Ok(r):
        assert r.actual_shape() == [2, 12]
    case Err(ShapeError.ReshapeElementsMismatch(input, output)):
        print("Element count mismatch: {input} -> {output}")
```

### Transpose

Swap two dimensions:

```simple
let t = TypedTensor.randn([DimSpec.exact(4), DimSpec.exact(8)])

let t_transposed = t.transpose(0, 1)?
assert t_transposed.actual_shape() == [8, 4]
```

### Reductions

Sum or mean along dimension:

```simple
let t = TypedTensor.randn([DimSpec.exact(3), DimSpec.exact(4)])

# Sum along dimension 1 (collapse to [3])
let s1 = t.sum(dim: 1)?
assert s1.ndim() == 1

# Sum with keepdim (keep dimension as 1)
let s2 = t.sum(dim: 1, keepdim: True)?
assert s2.actual_shape() == [3, 1]
```

---

## Runtime Verification

For dynamic or ranged dimensions, runtime verification ensures actual shapes satisfy constraints.

### Verify Method

```simple
let t = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(784)
])

match t.verify():
    case Ok(_):
        print("All dimensions valid")
    case Err(ShapeError.DimensionOutOfRange(dim_name, actual, min, max)):
        print("Dimension {dim_name} = {actual} not in [{min}, {max}]")
```

### Automatic Verification

Operations automatically verify results:

```simple
let a = TypedTensor.randn([DimSpec.ranged("batch", 32, 1, 64), DimSpec.exact(784)])
let w = TypedTensor.randn([DimSpec.exact(784), DimSpec.exact(256)])

# matmul automatically verifies output shape
let h = a.matmul(w)?  # Returns Err if dimensions incompatible
```

### Error Types

Common shape errors:

- `MatmulShapeMismatch(left, right)` - K dimensions don't match
- `BroadcastIncompatible(shapes)` - Shapes can't broadcast
- `ReshapeElementsMismatch(input, output)` - Element counts differ
- `DimensionOutOfRange(name, actual, min, max)` - Runtime dimension out of bounds
- `InferenceError(message)` - General inference failure

---

## Memory Estimation

Estimate memory usage from dimension bounds.

### TensorType Memory Methods

```simple
let tt = TensorType.new([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(256)
], DType.Float32)

# Minimum memory (min batch size)
let min_mem = tt.min_memory_bytes()
# 1 * 256 * 4 = 1024 bytes

# Maximum memory (max batch size)
let max_mem = tt.max_memory_bytes()
# 64 * 256 * 4 = 65536 bytes

# Sample memory (sample batch size)
let sample_mem = tt.sample_memory_bytes()
# 32 * 256 * 4 = 32768 bytes
```

### Memory Report

```simple
let t = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(784)
])

let report = MemoryReport.new(t.tensor_type())
print(report.to_string())
```

Output:
```
Memory Report for Tensor[batch: 1..64, 784], Float32:
  Min: 3136 bytes (0 MB)
  Max: 200704 bytes (0 MB)
  Sample: 100352 bytes (0 MB)
```

### Planning Training Memory

```simple
# Model parameters
let w1_mem = TensorType.new([DimSpec.exact(784), DimSpec.exact(256)], DType.Float32).min_memory_bytes()
let w2_mem = TensorType.new([DimSpec.exact(256), DimSpec.exact(10)], DType.Float32).min_memory_bytes()

# Activations (varies with batch size)
let act_type = TensorType.new([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(256)
], DType.Float32)

let min_act_mem = act_type.min_memory_bytes()
let max_act_mem = act_type.max_memory_bytes()

print("Parameters: {w1_mem + w2_mem} bytes")
print("Activations: {min_act_mem} - {max_act_mem} bytes")
print("Total range: {w1_mem + w2_mem + min_act_mem} - {w1_mem + w2_mem + max_act_mem} bytes")
```

---

## Advanced Patterns

### Neural Network Layers

```simple
fn linear_layer(input: TypedTensor, weight: TypedTensor, bias: TypedTensor) -> Result[TypedTensor, ShapeError]:
    # input: [batch, in_features]
    # weight: [in_features, out_features]
    # bias: [out_features]

    let output = input.matmul(weight)?
    return output.add(bias)
```

### Multi-Layer Network

```simple
struct MLPLayer:
    weight: TypedTensor
    bias: TypedTensor

fn forward(layers: List[MLPLayer], input: TypedTensor) -> Result[TypedTensor, ShapeError]:
    let mut x = input
    for layer in layers:
        x = linear_layer(x, layer.weight, layer.bias)?
    return Ok(x)
```

### Batch Matmul (3D Tensors)

```simple
# Batch matrix multiply: [B, M, K] @ [B, K, N] -> [B, M, N]
let a = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(4),
    DimSpec.exact(8)
])

let b = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(8),
    DimSpec.exact(16)
])

let c = a.matmul(b)?
# c has shape [batch, 4, 16]
```

### CNN with NCHW Format

```simple
# Typical CNN input: [batch, channels, height, width]
let input = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 128),
    DimSpec.exact(3),    # RGB
    DimSpec.exact(224),  # Height
    DimSpec.exact(224)   # Width
])

# Verify NCHW format
assert input.ndim() == 4
assert input.actual_shape()[1] == 3  # 3 channels
```

### Transformer Attention

```simple
# Q, K, V: [batch, heads, seq_len, head_dim]
let batch = DimSpec.ranged("batch", 32, 1, 64)
let heads = DimSpec.exact(12)
let seq_len = DimSpec.ranged("seq", 128, 1, 512)
let head_dim = DimSpec.exact(64)

let q = TypedTensor.randn([batch, heads, seq_len, head_dim])
let k = TypedTensor.randn([batch, heads, seq_len, head_dim])
let v = TypedTensor.randn([batch, heads, seq_len, head_dim])

# Attention scores: Q @ K^T
let k_t = k.transpose(2, 3)?  # [batch, heads, head_dim, seq]
let scores = q.matmul(k_t)?   # [batch, heads, seq, seq]
```

---

## Troubleshooting

### Shape Mismatch Errors

**Problem:** Matmul fails with shape mismatch

```simple
let a = TypedTensor.randn([DimSpec.exact(4), DimSpec.exact(8)])
let b = TypedTensor.randn([DimSpec.exact(10), DimSpec.exact(16)])
let c = a.matmul(b)?  # Error: K dimensions don't match (8 vs 10)
```

**Solution:** Ensure contraction dimension matches

```simple
let b_correct = TypedTensor.randn([DimSpec.exact(8), DimSpec.exact(16)])
let c = a.matmul(b_correct)?  # OK: [4, 8] @ [8, 16] -> [4, 16]
```

### Dimension Out of Range

**Problem:** Runtime dimension exceeds range

```simple
let t = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(256)
])
# If actual batch size is 128, verify() will fail
```

**Solution:** Adjust range or fix batch size

```simple
let t_correct = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 256),  # Increased max to 256
    DimSpec.exact(256)
])
```

### Reshape Element Count Mismatch

**Problem:** Reshape changes element count

```simple
let t = TypedTensor.randn([DimSpec.exact(4), DimSpec.exact(6)])  # 24 elements
let r = t.reshape([DimSpec.exact(3), DimSpec.exact(10)])?        # 30 elements - ERROR
```

**Solution:** Ensure element count is preserved

```simple
let r_correct = t.reshape([DimSpec.exact(2), DimSpec.exact(12)])?  # 24 elements - OK
```

### Memory Estimation Returns Infinity

**Problem:** Dynamic dimensions prevent memory estimation

```simple
let t = TypedTensor.randn([
    DimSpec.dynamic(),
    DimSpec.exact(256)
])
let mem = t.tensor_type().max_memory_bytes()  # May be very large or infinite
```

**Solution:** Use ranged dimensions for meaningful bounds

```simple
let t_bounded = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(256)
])
let mem = t_bounded.tensor_type().max_memory_bytes()  # Finite: 64 * 256 * 4
```

---

## Best Practices

### 1. Use Exact Dimensions for Fixed Shapes

```simple
# Good: Clear that images are always 224x224
let img = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(3),
    DimSpec.exact(224),
    DimSpec.exact(224)
])

# Avoid: Makes image size seem variable
let img_bad = TypedTensor.randn([
    DimSpec.dynamic(),
    DimSpec.dynamic(),
    DimSpec.dynamic(),
    DimSpec.dynamic()
])
```

### 2. Name Dimensions Semantically

```simple
# Good: Clear what each dimension represents
let embeddings = TypedTensor.randn([
    DimSpec.named("batch", 32),
    DimSpec.named("seq_len", 128),
    DimSpec.named("embed_dim", 512)
])

# Avoid: No semantic meaning
let embeddings_bad = TypedTensor.randn([
    DimSpec.exact(32),
    DimSpec.exact(128),
    DimSpec.exact(512)
])
```

### 3. Set Realistic Range Bounds

```simple
# Good: Realistic batch size range
let data = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 256),
    DimSpec.exact(784)
])

# Avoid: Unrealistic upper bound wastes memory estimation
let data_bad = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 1000000),
    DimSpec.exact(784)
])
```

### 4. Check Errors Explicitly

```simple
# Good: Handle shape errors gracefully
match model_forward(input):
    case Ok(output):
        process(output)
    case Err(ShapeError.MatmulShapeMismatch(left, right)):
        print("Shape error: expected {left} @ {right}")
        return Err(...)
    case Err(e):
        print("Other error: {e}")
        return Err(...)

# Avoid: Unwrap without checking
let output = model_forward(input).unwrap()  # Panics on shape error
```

### 5. Document Dimension Contracts

```simple
"""
Forward pass through MLP.

Args:
    input: [batch, 784] - Flattened MNIST images
    w1: [784, 256] - First layer weights
    w2: [256, 10] - Second layer weights

Returns:
    [batch, 10] - Logits for 10 classes
"""
fn mlp_forward(input: TypedTensor, w1: TypedTensor, w2: TypedTensor) -> Result[TypedTensor, ShapeError]:
    let h1 = input.matmul(w1)?
    let output = h1.matmul(w2)?
    return Ok(output)
```

---

## See Also

- [Design Documentation](../design/tensor_dimensions_design.md) - Architecture and implementation details
- [Feature Specification](../spec/generated/tensor_dimensions.md) - Formal specification
- [Test Specification](../../simple/std_lib/test/features/data_structures/tensor_dimensions_spec.spl) - BDD tests
- [PyTorch Integration](../../simple/std_lib/src/ml/torch/README.md) - PyTorch wrapper overview

---

**Last Updated:** 2026-01-10
**Status:** Implementing
