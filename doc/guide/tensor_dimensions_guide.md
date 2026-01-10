# Tensor Dimension Inference - User Guide

**Status:** Implementing
**Feature ID:** #193
**Related:** Tensor Literals (#192), Type Inference (#8-9)

## Introduction

Tensor dimension inference brings compile-time dimension tracking to Simple's tensor operations. This feature enables:

- **Shape Verification**: Catch dimension mismatches at compile time before runtime
- **Named Dimensions**: Document tensor shapes with meaningful names like "batch", "sequence", "channels"
- **Range Constraints**: Specify minimum and maximum sizes for dynamic dimensions
- **Memory Estimation**: Calculate memory requirements from dimension bounds
- **Type Safety**: Ensure operations like matmul, reshape, and broadcast are dimensionally correct

## Quick Start

Here's a simple example showing basic dimension tracking with the standalone API:

```simple
# Define dimension types
enum Dim:
    Literal(value: Int)
    Named(name: String, lo: Int, hi: Int)
    Unknown

struct TensorShape:
    dims: List[Dim]

# Create shapes
let input_shape = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Literal(value: 784)
])

let weight_shape = TensorShape(dims: [
    Dim.Literal(value: 784),
    Dim.Literal(value: 10)
])

# Shape inference for matmul: [batch:1..64, 784] @ [784, 10] -> [batch:1..64, 10]
```

## Dimension Specifications

### Exact Dimensions

Use `Dim.Literal(value: n)` for fixed dimensions known at compile time:

```simple
let image_shape = TensorShape(dims: [
    Dim.Literal(value: 3),    # RGB channels
    Dim.Literal(value: 224),  # Height
    Dim.Literal(value: 224)   # Width
])  # Shape: [3, 224, 224]
```

### Named Dimensions with Ranges

Use `Dim.Named(name, lo, hi)` for dynamic dimensions with constraints:

```simple
let batch_shape = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 128),
    Dim.Named(name: "seq", lo: 1, hi: 512),
    Dim.Literal(value: 768)
])  # Shape: [batch:1..128, seq:1..512, 768]
```

Benefits of named dimensions:
- Self-documenting code
- Memory estimation with min/max bounds
- Runtime validation of constraints
- Better error messages

### Unknown Dimensions

Use `Dim.Unknown` when the dimension is completely unknown:

```simple
let variable_shape = TensorShape(dims: [
    Dim.Literal(value: 10),
    Dim.Unknown   # Unknown size
])  # Shape: [10, *]
```

## Shape Inference Operations

### Matrix Multiplication (matmul)

Shape inference for `matmul` verifies K dimensions match:

```simple
# [M, K] @ [K, N] -> [M, N]
let a_shape = TensorShape(dims: [Dim.Literal(value: 4), Dim.Literal(value: 8)])
let b_shape = TensorShape(dims: [Dim.Literal(value: 8), Dim.Literal(value: 16)])

let result = infer_matmul_shape(a_shape, b_shape)
# Result: [4, 16] ✓
```

With named dimensions:

```simple
let input = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Literal(value: 784)
])
let weight = TensorShape(dims: [
    Dim.Literal(value: 784),
    Dim.Literal(value: 256)
])

let hidden = infer_matmul_shape(input, weight)
# Shape: [batch:1..64, 256]
# Named dimension preserved!
```

### Error Detection

Shape mismatches are caught during inference:

```simple
let input = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Literal(value: 784)
])
let bad_weight = TensorShape(dims: [
    Dim.Literal(value: 512),  # Wrong! Should be 784
    Dim.Literal(value: 10)
])

let result = infer_matmul_shape(input, bad_weight)
# Error: K dimensions don't match (784 vs 512) ✗
```

## Multi-Layer Networks

Dimension inference propagates through network layers:

```simple
# MNIST classifier: 784 -> 256 -> 10
let input = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Literal(value: 784)
])

let w1 = TensorShape(dims: [
    Dim.Literal(value: 784),
    Dim.Literal(value: 256)
])

let w2 = TensorShape(dims: [
    Dim.Literal(value: 256),
    Dim.Literal(value: 10)
])

# Forward pass with shape tracking
match infer_matmul_shape(input, w1):
    case ShapeResult.Ok(h1):
        match infer_matmul_shape(h1, w2):
            case ShapeResult.Ok(output):
                # output shape: [batch:1..64, 10] ✓
                print("Success!")
            case ShapeResult.Err(e):
                print("Layer 2 failed")
    case ShapeResult.Err(e):
        print("Layer 1 failed")
```

## Memory Estimation

Calculate memory requirements from dimension bounds:

```simple
struct MemoryBounds:
    min_bytes: Int
    max_bytes: Int

fn estimate_memory(shape: TensorShape, elem_size: Int) -> MemoryBounds:
    let mut min_elems = 1
    let mut max_elems = 1

    for d in shape.dims:
        match d:
            case Dim::Literal(v):
                min_elems = min_elems * v
                max_elems = max_elems * v
            case Dim::Named(_, lo, hi):
                min_elems = min_elems * lo
                max_elems = max_elems * hi
            case _:
                min_elems = min_elems * 1
                max_elems = max_elems * 1000

    return MemoryBounds(
        min_bytes: min_elems * elem_size,
        max_bytes: max_elems * elem_size
    )
```

Use this to:
- Plan GPU memory allocation
- Validate model fits on device
- Optimize batch sizes
- Detect memory issues early

## CNN Example (NCHW Format)

```simple
# Input: [batch, channels, height, width]
let cnn_input = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 128),
    Dim.Literal(value: 3),      # RGB
    Dim.Literal(value: 224),    # Height
    Dim.Literal(value: 224)     # Width
])  # Shape: [batch:1..128, 3, 224, 224]

let mem = estimate_memory(cnn_input, 4)  # Float32
print("Memory: {mem.min_bytes / 1024 / 1024} - {mem.max_bytes / 1024 / 1024} MB")
```

## Best Practices

### 1. Use Named Dimensions for Documentation

```simple
# ✓ Good: Self-documenting
let embeddings = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Named(name: "seq_len", lo: 1, hi: 512),
    Dim.Literal(value: 768)  # embedding_dim
])

# ✗ Avoid: Hard to understand
let embeddings = TensorShape(dims: [
    Dim.Named(name: "d0", lo: 1, hi: 64),
    Dim.Named(name: "d1", lo: 1, hi: 512),
    Dim.Literal(value: 768)
])
```

### 2. Specify Realistic Bounds

```simple
# ✓ Good: Realistic constraints
Dim.Named(name: "batch", lo: 1, hi: 128)  # GPU fits up to 128

# ✗ Avoid: Unrealistic bounds
Dim.Named(name: "batch", lo: 1, hi: 1000000)  # Won't fit on GPU
```

### 3. Use Exact Dimensions When Possible

```simple
# ✓ Good: Fixed architecture
let weight = TensorShape(dims: [
    Dim.Literal(value: 784),   # MNIST input size
    Dim.Literal(value: 10)     # Output classes
])

# ✗ Avoid: Unnecessary dynamic dimensions
let weight = TensorShape(dims: [
    Dim.Unknown,
    Dim.Unknown
])
```

## Troubleshooting

### Common Errors

**MatmulIncompatible**: K dimensions don't match
```simple
let a = TensorShape(dims: [Dim.Literal(value: 4), Dim.Literal(value: 8)])
let b = TensorShape(dims: [Dim.Literal(value: 10), Dim.Literal(value: 16)])
# Error: 8 != 10
```

**RankMismatch**: Tensor ranks don't match
```simple
let a = TensorShape(dims: [Dim.Literal(value: 4)])  # 1D
let b = TensorShape(dims: [Dim.Literal(value: 4), Dim.Literal(value: 8)])  # 2D
# Error: matmul requires 2D tensors
```

**ReshapeMismatch**: Element count mismatch
```simple
let t = TensorShape(dims: [Dim.Literal(value: 4), Dim.Literal(value: 6)])  # 24 elements
# Reshape to 25 elements fails: 24 != 25
```

### Debugging Tips

1. **Print shapes**: Use `shape_to_string()` to inspect tensor dimensions
2. **Check bounds**: Verify range constraints are realistic
3. **Test incrementally**: Verify each operation in isolation
4. **Use exact dims for debugging**: Replace ranges with exact values temporarily

## Examples

See working examples at:
- `simple/std_lib/example/ml/tensor_dimensions_demo.spl` - Complete demo with all features
- `simple/std_lib/example/ml/tensor_dimensions_complete.spl` - Comprehensive implementation
- `simple/std_lib/test/unit/ml/torch/typed_tensor_spec.spl` - Test suite

## Future Enhancements

Planned features:
- TypedTensor class integration (blocked by module system)
- Einsum notation with dimension inference
- Symbolic dimension expressions
- Compile-time memory bound checking
- Integration with GPU kernel generators
- Lean formal verification of shape inference rules

## Summary

Tensor dimension inference provides:
- ✅ Compile-time shape verification
- ✅ Self-documenting code with named dimensions
- ✅ Memory estimation and planning
- ✅ Type-safe neural network construction
- ✅ Early error detection

By using dimension inference, you catch shape mismatches before runtime, document tensor semantics clearly, and build more robust ML code.
