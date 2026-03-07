# Tensor Dimension Inference

**Version:** 0.5.0
**Status:** Production Ready (Standalone Mode)

---

## Overview

Tensor dimension inference provides compile-time shape verification for neural network operations. Catch dimension mismatches before running your model.

**Features:**
- Shape verification at compile time
- Named dimensions with range constraints
- Memory estimation from dimension bounds
- Matmul, broadcast, and reshape validation

---

## Quick Start

```simple
fn main():
    let input = TensorShape(dims: [
        Dim.Named(name: "batch", lo: 1, hi: 32),
        Dim.Literal(value: 784)
    ])

    let weight = TensorShape(dims: [
        Dim.Literal(value: 784),
        Dim.Literal(value: 10)
    ])

    match infer_matmul_shape(input, weight):
        case ShapeResult.Ok(output):
            print("Output shape: {shape_to_string(output)}")
            # Output: [batch:1..32, 10]
        case ShapeResult.Err(e):
            print("Error: dimension mismatch!")
```

Copy the working example to get started:

```bash
cp simple/std_lib/example/ml/tensor_dimensions_standalone_demo.spl my_program.spl
```

---

## Dimension Specifications

### Exact Dimensions

Use `Dim.Literal(value: n)` for fixed sizes:

```simple
let image = TensorShape(dims: [
    Dim.Literal(value: 3),    # RGB channels
    Dim.Literal(value: 224),  # Height
    Dim.Literal(value: 224)   # Width
])
# Shape: [3, 224, 224]
```

### Named Dimensions with Ranges

Use `Dim.Named(name, lo, hi)` for dynamic dimensions with constraints:

```simple
let batch_input = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 128),
    Dim.Named(name: "seq", lo: 1, hi: 512),
    Dim.Literal(value: 768)
])
# Shape: [batch:1..128, seq:1..512, 768]
```

### Unknown Dimensions

Use `Dim.Unknown` when the dimension is completely unconstrained:

```simple
let variable = TensorShape(dims: [
    Dim.Literal(value: 10),
    Dim.Unknown
])
# Shape: [10, *]
```

---

## Shape Inference Operations

### Matrix Multiplication

```simple
# [M, K] @ [K, N] -> [M, N]
let a = TensorShape(dims: [Dim.Literal(value: 4), Dim.Literal(value: 8)])
let b = TensorShape(dims: [Dim.Literal(value: 8), Dim.Literal(value: 16)])

let result = infer_matmul_shape(a, b)
# Result: [4, 16]
```

With named dimensions (preserved through operations):

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
```

### Error Detection

```simple
let bad_weight = TensorShape(dims: [
    Dim.Literal(value: 512),  # Wrong! Should be 784
    Dim.Literal(value: 10)
])

let result = infer_matmul_shape(input, bad_weight)
# Error: K dimensions don't match (784 vs 512)
```

### Reshape Validation

```simple
let original = TensorShape(dims: [
    Dim.Literal(value: 2),
    Dim.Literal(value: 3),
    Dim.Literal(value: 4)
])

let target = TensorShape(dims: [
    Dim.Literal(value: 6),
    Dim.Literal(value: 4)
])

match verify_reshape(original, target):
    case ShapeResult.Ok(_): print("Valid reshape: 2*3*4 = 6*4 = 24")
    case ShapeResult.Err(_): print("Invalid: element count differs")
```

### Broadcasting

```simple
let a = TensorShape(dims: [Dim.Literal(value: 3), Dim.Literal(value: 1)])
let b = TensorShape(dims: [Dim.Literal(value: 1), Dim.Literal(value: 4)])

let result = infer_broadcast_shape(a, b)
# Result: [3, 4]
```

---

## Multi-Layer Network Validation

Validate an entire network's shape chain at once:

```simple
fn validate_network():
    let input = TensorShape(dims: [
        Dim.Named(name: "batch", lo: 1, hi: 128),
        Dim.Literal(value: 784)
    ])

    let layers = [
        TensorShape(dims: [Dim.Literal(value: 784), Dim.Literal(value: 512)]),
        TensorShape(dims: [Dim.Literal(value: 512), Dim.Literal(value: 256)]),
        TensorShape(dims: [Dim.Literal(value: 256), Dim.Literal(value: 10)])
    ]

    let mut current = input
    let mut layer_num = 1

    for weight in layers:
        match infer_matmul_shape(current, weight):
            case ShapeResult.Ok(next):
                print("Layer {layer_num}: {shape_to_string(next)}")
                current = next
                layer_num = layer_num + 1
            case ShapeResult.Err(e):
                print("ERROR at layer {layer_num}: {e}")
                return

    print("All layers validated")
```

Output:
```
Layer 1: [batch:1..128, 512]
Layer 2: [batch:1..128, 256]
Layer 3: [batch:1..128, 10]
All layers validated
```

---

## Memory Estimation

Calculate memory bounds from dimension ranges:

```simple
fn estimate_memory(shape: TensorShape, elem_size: Int) -> (Int, Int):
    let mut min_elems = 1
    let mut max_elems = 1

    for d in shape.dims:
        match d:
            case Dim.Literal(v):
                min_elems = min_elems * v
                max_elems = max_elems * v
            case Dim.Named(_, lo, hi):
                min_elems = min_elems * lo
                max_elems = max_elems * hi
            case _:
                min_elems = min_elems * 1
                max_elems = max_elems * 10000

    (min_elems * elem_size, max_elems * elem_size)

# Example: CNN input [batch:1..128, 3, 224, 224]
let cnn_input = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 128),
    Dim.Literal(value: 3),
    Dim.Literal(value: 224),
    Dim.Literal(value: 224)
])

let (min_bytes, max_bytes) = estimate_memory(cnn_input, 4)  # Float32
print("Memory: {min_bytes / 1024 / 1024}-{max_bytes / 1024 / 1024} MB")
# Memory: 0-73 MB
```

---

## Runtime Shape Verification

Verify actual tensor shapes against expected specifications:

```simple
fn verify_runtime_shape(actual: List<Int>, expected: TensorShape) -> Bool:
    if actual.len() != expected.ndim():
        return false

    let mut i = 0
    while i < actual.len():
        let actual_dim = actual[i]
        let expected_dim = expected.dims[i]

        let valid: Bool
        match expected_dim:
            case Dim.Literal(v):
                valid = (actual_dim == v)
            case Dim.Named(_, lo, hi):
                valid = (actual_dim >= lo and actual_dim <= hi)
            case _:
                valid = true

        if not valid:
            return false
        i = i + 1

    true
```

---

## Dimension Error Codes

When shape verification fails, specific error codes identify the problem:

### E0501: Dimension Mismatch

Adjacent layer dimensions do not match.

```
Error E0501: Dimension mismatch
  Layer 1 output: 512
  Layer 2 input:  256
  Fix: Change layer 2 input to 512 or layer 1 output to 256
```

### E0502: Layer Incompatible

Layer types cannot be connected (e.g., Linear output to Conv2d input without reshape).

```
Error E0502: Layer incompatible
  Linear output: [batch, 256]
  Conv2d expects: [batch, channels, height, width]
  Fix: Add reshape between layers
```

### E0503: Rank Mismatch

Tensors have different numbers of dimensions.

```
Error E0503: Rank mismatch
  Left:  3 dimensions [batch, seq, features]
  Right: 2 dimensions [features, output]
  Fix: Check operation requirements
```

### E0504: MatMul Incompatible

Inner dimensions of matrix multiplication do not match.

```
Error E0504: MatMul incompatible
  A shape: [32, 784]
  B shape: [512, 10]
  K mismatch: 784 != 512
  Fix: Change B first dimension to 784
```

### E0505: Broadcast Incompatible

Shapes cannot be broadcast together.

```
Error E0505: Broadcast incompatible
  A: [3, 4]
  B: [5, 4]
  Dimension 0: 3 != 5 (neither is 1)
  Fix: Use explicit reshape or tile
```

### E0506: Batch Dimension Mismatch

Batch sizes do not match between tensors.

```
Error E0506: Batch dimension mismatch
  Input batch: 32
  Target batch: 64
  Fix: Ensure consistent batch sizes
```

### E0507: Channel Mismatch

Number of channels does not match expected value.

```
Error E0507: Channel mismatch
  Input channels: 3
  Conv2d in_channels: 1
  Fix: Set in_channels to 3 for RGB input
```

### E0508: Sequence Length Mismatch

Sequence dimensions do not match between encoder and decoder.

```
Error E0508: Sequence length mismatch
  Encoder output seq: 128
  Decoder expected seq: 256
  Fix: Check sequence padding/truncation
```

### E0509: Dimension Out of Range

A dimension value exceeds its specified range constraint.

```
Error E0509: Dimension out of range
  Dimension "batch": actual=256, range=1..128
  Fix: Reduce batch size or increase range upper bound
```

### E0510: Unresolved Dimension Variable

A named dimension could not be resolved during inference.

```
Error E0510: Unresolved dimension variable
  Variable: "hidden_size"
  Fix: Provide explicit dimension or add constraint
```

---

## API Reference

### Types

```simple
enum Dim:
    Literal(value: Int)                    # Fixed dimension
    Named(name: text, lo: Int, hi: Int)    # Named with range
    Unknown                                 # Unconstrained

class TensorShape:
    dims: List<Dim>

    fn ndim() -> Int               # Number of dimensions
    fn is_scalar() -> Bool         # ndim == 0
    fn total_elements() -> Int     # Product of dimensions (Literal only)

enum ShapeResult:
    Ok(shape: TensorShape)
    Err(error: ShapeError)

enum ShapeError:
    MatmulIncompatible(k1: Int, k2: Int)
    RankMismatch(rank1: Int, rank2: Int)
    ReshapeMismatch(elements1: Int, elements2: Int)
    BroadcastIncompatible(dim: Int, size1: Int, size2: Int)
```

### Functions

```simple
fn infer_matmul_shape(a: TensorShape, b: TensorShape) -> ShapeResult
fn infer_broadcast_shape(a: TensorShape, b: TensorShape) -> ShapeResult
fn verify_reshape(input: TensorShape, output: TensorShape) -> ShapeResult
fn unify_dims(d1: Dim, d2: Dim) -> Option<Dim>
fn shape_to_string(shape: TensorShape) -> text
```

---

## Current Limitations

### Module Imports

Module system does not support compile-time cross-module type resolution yet. Use standalone mode with inline type definitions.

### FFI Operations

Runtime does not support `.as_ptr()` on List types for FFI calls. Use dimension inference for shape checking only; for actual tensor computation, use separate PyTorch tensors.

---

## Best Practices

1. **Use named dimensions** for self-documenting shapes (e.g., "batch", "seq", "channels")
2. **Specify realistic bounds** (e.g., batch 1..128, not 1..1000000)
3. **Use exact dimensions** for fixed architecture weights
4. **Validate before training** to catch shape errors early
5. **Print shapes** with `shape_to_string()` for debugging
6. **Test incrementally** -- validate one layer at a time, then chain
7. **Keep files under 200 lines** (large files may terminate early in standalone mode)

---

## Troubleshooting

| Error | Cause | Fix |
|-------|-------|-----|
| `MatmulIncompatible` | K dimensions don't match | Fix inner dimensions |
| `RankMismatch` | Different number of dims | Flatten or reshape |
| `ReshapeMismatch` | Element count differs | Check total elements match |
| "Unexpected token" | Reserved keywords or Unicode | Use ASCII, avoid `vec`/`mat` as names |
| "undefined identifier: ShapeError" | Module import attempted | Use standalone mode |

---

## Working Examples

| File | Description |
|------|-------------|
| `tensor_dimensions_standalone_demo.spl` | Basic dimension inference |
| `tensor_dimensions_spec.spl` | Executable specification |
| `tensor_inference_integration.spl` | Integration test workflows |
| `reshape_examples.spl` | Reshape validation |

---

## Related Documentation

- Deep learning guide: `doc/guide/deep_learning/deep_learning.md`
- GPU programming: `doc/guide/backend/gpu_programming.md`
- Source: `src/lib/verification/models/tensor_dimensions.spl`
