# Tensor Dimension Inference

**Status:** Production Ready (Standalone Mode)
**Feature ID:** #193
**Related:** Tensor Literals (#192), Type Inference (#8-9)

## Introduction

Tensor dimension inference brings compile-time dimension tracking to Simple's tensor operations:

- **Shape Verification**: Catch dimension mismatches at compile time
- **Named Dimensions**: Document tensor shapes with meaningful names like "batch", "sequence", "channels"
- **Range Constraints**: Specify minimum and maximum sizes for dynamic dimensions
- **Memory Estimation**: Calculate memory requirements from dimension bounds
- **Type Safety**: Ensure operations like matmul, reshape, and broadcast are dimensionally correct

---

## Quick Start

### From Working Example (Recommended)

```bash
cp simple/std_lib/example/ml/tensor_dimensions_standalone_demo.spl my_tensor_program.spl
```

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
        case ShapeResult.Err(e):
            print("Error: dimension mismatch!")
```

### Manual Setup

Copy type definitions from `simple/std_lib/src/verification/models/tensor_dimensions.spl`:

1. Enum `Dim` (lines 13-53)
2. Enum `ShapeError` (lines 206-235)
3. Class `TensorShape` (lines 105-159)
4. Functions: `unify_dims`, `infer_matmul_shape`, `infer_broadcast_shape`, `verify_reshape`

---

## Dimension Specifications

### Exact Dimensions

Use `Dim.Literal(value: n)` for fixed dimensions:

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

### Unknown Dimensions

Use `Dim.Unknown` when the dimension is completely unknown:

```simple
let variable_shape = TensorShape(dims: [
    Dim.Literal(value: 10),
    Dim.Unknown   # Unknown size
])  # Shape: [10, *]
```

---

## Shape Inference Operations

### Matrix Multiplication (matmul)

```simple
# [M, K] @ [K, N] -> [M, N]
let a_shape = TensorShape(dims: [Dim.Literal(value: 4), Dim.Literal(value: 8)])
let b_shape = TensorShape(dims: [Dim.Literal(value: 8), Dim.Literal(value: 16)])

let result = infer_matmul_shape(a_shape, b_shape)
# Result: [4, 16]
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
# Shape: [batch:1..64, 256] - Named dimension preserved
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

---

## Common Use Cases

### Multi-Layer Network Validation

```simple
fn validate_network_shapes():
    let input = TensorShape(dims: [
        Dim.Named(name: "batch", lo: 1, hi: 128),
        Dim.Literal(value: 784)
    ])

    let layers = [
        TensorShape(dims: [Dim.Literal(value: 784), Dim.Literal(value: 512)]),
        TensorShape(dims: [Dim.Literal(value: 512), Dim.Literal(value: 256)]),
        TensorShape(dims: [Dim.Literal(value: 256), Dim.Literal(value: 10)])
    ]

    let mut current_shape = input
    let mut layer_num = 1

    for weight in layers:
        match infer_matmul_shape(current_shape, weight):
            case ShapeResult.Ok(next_shape):
                print("Layer {layer_num}: {shape_to_string(next_shape)}")
                current_shape = next_shape
                layer_num = layer_num + 1
            case ShapeResult.Err(e):
                print("ERROR at layer {layer_num}")
                return

    print("All layers validated")
```

### Memory Estimation

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

# CNN input: [batch:1..128, 3, 224, 224]
let cnn_input = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 128),
    Dim.Literal(value: 3),
    Dim.Literal(value: 224),
    Dim.Literal(value: 224)
])

let (min_bytes, max_bytes) = estimate_memory(cnn_input, 4)  # Float32
print("Memory: {min_bytes / 1024 / 1024}-{max_bytes / 1024 / 1024} MB")
```

### Reshape Validation

```simple
fn validate_reshape(input_dims: List<Int>, output_dims: List<Int>) -> Bool:
    let input_shape = TensorShape(dims: [
        for d in input_dims: Dim.Literal(value: d)
    ])
    let output_shape = TensorShape(dims: [
        for d in output_dims: Dim.Literal(value: d)
    ])

    match verify_reshape(input_shape, output_shape):
        case ShapeResult.Ok(_): true
        case ShapeResult.Err(_): false
```

### Runtime Shape Verification

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

## Current Limitations

### Module Imports Don't Work

Module system doesn't support compile-time cross-module type resolution yet.

**Workaround:** Use standalone mode with inline type definitions.

### FFI Operations Stubbed

Runtime doesn't support `.as_ptr()` on List types needed for FFI calls.

**Workaround:** Use dimension inference for shape checking only. For actual tensor operations, use regular PyTorch tensors separately.

---

## Best Practices

1. **Use named dimensions** for self-documenting code
2. **Specify realistic bounds** (e.g., batch 1..128, not 1..1000000)
3. **Use exact dimensions** when possible (fixed architecture weights)
4. **Validate before training** to catch shape errors early
5. **Keep files <200 lines** (large files may terminate early)

---

## Troubleshooting

| Error | Cause | Fix |
|-------|-------|-----|
| MatmulIncompatible | K dimensions don't match | Fix inner dimensions |
| RankMismatch | Different number of dims | Flatten/reshape |
| ReshapeMismatch | Element count differs | Check total elements |
| "Unexpected token" | Reserved keywords or Unicode | Use ASCII, avoid `vec`/`mat` |
| "undefined identifier: ShapeError" | Module import attempted | Use standalone mode |

**Debugging tips:** Print shapes with `shape_to_string()`, test incrementally, replace ranges with exact values temporarily.

---

## Working Examples

- `tensor_dimensions_standalone_demo.spl` - Basic dimension inference
- `tensor_dimensions_spec.spl` - Executable specification
- `tensor_inference_integration.spl` - Integration test workflows
- `reshape_examples.spl` - Reshape validation

## Future Enhancements

- TypedTensor class integration (blocked by module system)
- Einsum notation with dimension inference
- Symbolic dimension expressions
- Compile-time memory bound checking
- Integration with GPU kernel generators
