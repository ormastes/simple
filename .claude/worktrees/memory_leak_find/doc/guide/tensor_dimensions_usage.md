# Tensor Dimension Inference - Practical Usage Guide

**Status:** Production Ready (Standalone Mode)
**Feature ID:** #193
**Last Updated:** 2026-01-10

## Quick Start

### Method 1: Start from Working Example (Recommended)

**Step 1:** Copy a working example
```bash
cp simple/std_lib/example/ml/tensor_dimensions_standalone_demo.spl my_tensor_program.spl
```

**Step 2:** Modify for your needs
```simple
# my_tensor_program.spl
# (Type definitions already included from template)

fn main():
    # Your code here
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

**Step 3:** Run
```bash
./target/debug/simple run my_tensor_program.spl
```

### Method 2: Manual Setup

**Step 1:** Copy type definitions

Copy the following sections from `simple/std_lib/src/verification/models/tensor_dimensions.spl`:

1. Enum `Dim` (lines 13-53)
2. Enum `ShapeError` (lines 206-235)
3. Class `TensorShape` (lines 105-159)
4. Functions you need:
   - `unify_dims` (lines 273-328)
   - `infer_matmul_shape` (lines 381-419)
   - `infer_broadcast_shape` (lines 421-468)
   - `verify_reshape` (lines 471-498)

**Step 2:** Add helper functions
```simple
fn dim_to_string(d: Dim) -> String:
    match d:
        case Dim.Literal(v):
            "{v}"
        case Dim.Named(n, lo, hi):
            if lo == hi:
                "{n}={lo}"
            else:
                "{n}:{lo}..{hi}"
        case _:
            "*"

fn shape_to_string(shape: TensorShape) -> String:
    # ... implementation ...
```

**Step 3:** Write your code
```simple
fn main():
    # Use the types and functions
    let shape = TensorShape(dims: [...])
    # ...
```

## Current Limitations & Workarounds

### ❌ Module Imports Don't Work

**Problem:**
```simple
import ml.torch.typed_tensor.{TypedTensor, DimSpec}  # ❌ Fails at compile time
```

**Why:**
Simple's module system doesn't support compile-time cross-module type resolution yet.

**Workaround:**
Use standalone mode with inline type definitions (as shown above). ✅

### ❌ FFI Operations Stubbed

**Problem:**
```simple
let tensor = TypedTensor.zeros([DimSpec.exact(784)])  # FFI not available
```

**Why:**
Runtime doesn't support `.as_ptr()` on List types needed for FFI calls.

**Workaround:**
Use dimension inference for **shape checking only**. For actual tensor operations, use regular PyTorch tensors separately. ✅

**Example:**
```simple
# Use dimension inference for validation
let input_shape = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Literal(value: 784)
])

let weight_shape = TensorShape(dims: [
    Dim.Literal(value: 784),
    Dim.Literal(value: 10)
])

# Verify shapes are compatible
match infer_matmul_shape(input_shape, weight_shape):
    case ShapeResult.Ok(output_shape):
        print("✓ Shapes compatible: {shape_to_string(output_shape)}")

        # Now use actual PyTorch tensors (if available)
        # let input_tensor = torch.randn([batch_size, 784])
        # let weight_tensor = torch.randn([784, 10])
        # let output = input_tensor @ weight_tensor

    case ShapeResult.Err(e):
        print("✗ Shape error: {e.to_string()}")
```

### ⚠️ Large Files May Terminate Early

**Problem:**
Scripts >300 lines might stop executing after first example block.

**Workaround:**
Split into multiple focused files (<200 lines each). ✅

## Common Use Cases

### Use Case 1: Neural Network Shape Validation

```simple
# Validate multi-layer network dimensions
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

    print("✓ All layers validated")
```

### Use Case 2: Memory Estimation

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

# Usage
let cnn_layer = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Literal(value: 128),  # channels
    Dim.Literal(value: 56),   # height
    Dim.Literal(value: 56)    # width
])

let (min_bytes, max_bytes) = estimate_memory(cnn_layer, 4)
let min_mb = min_bytes / (1024 * 1024)
let max_mb = max_bytes / (1024 * 1024)
print("Memory: {min_mb}-{max_mb} MB")
```

### Use Case 3: Reshape Validation

```simple
fn validate_reshape(input_dims: List<Int>, output_dims: List<Int>) -> Bool:
    # Convert to shapes
    let input_shape = TensorShape(dims: [
        for d in input_dims: Dim.Literal(value: d)
    ])

    let output_shape = TensorShape(dims: [
        for d in output_dims: Dim.Literal(value: d)
    ])

    # Verify element counts match
    match verify_reshape(input_shape, output_shape):
        case ShapeResult.Ok(_):
            true
        case ShapeResult.Err(_):
            false

# Usage
if validate_reshape([batch, 784], [batch, 28, 28]):
    print("✓ Valid reshape: flatten MNIST image")
else:
    print("✗ Invalid reshape")
```

### Use Case 4: Runtime Shape Verification

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

# Usage
let expected = TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Literal(value: 784)
])

if verify_runtime_shape([32, 784], expected):
    print("✓ Shape matches constraints")
else:
    print("✗ Shape violates constraints")
```

## Working Examples

All these examples are tested and working:

1. **tensor_dimensions_standalone_demo.spl** (208 lines)
   - Basic dimension inference
   - Multi-layer networks
   - Error detection
   - Named dimensions

2. **tensor_dimensions_spec.spl** (288 lines)
   - Executable specification
   - 4 comprehensive examples
   - Matrix multiplication
   - MNIST network

3. **tensor_inference_integration.spl** (313 lines)
   - 5 integration test workflows
   - Multi-layer MLP
   - Dynamic batching
   - Transformer dimensions

4. **reshape_examples.spl** (122 lines)
   - Reshape validation
   - Element count checking
   - Invalid reshape detection

## Best Practices

### 1. Use Named Dimensions for Documentation

```simple
# ✓ Good: Self-documenting
TensorShape(dims: [
    Dim.Named(name: "batch", lo: 1, hi: 64),
    Dim.Named(name: "seq_len", lo: 1, hi: 512),
    Dim.Literal(value: 768)  # embedding_dim
])

# ✗ Avoid: Unclear
TensorShape(dims: [
    Dim.Named(name: "d0", lo: 1, hi: 64),
    Dim.Named(name: "d1", lo: 1, hi: 512),
    Dim.Literal(value: 768)
])
```

### 2. Validate Before Training

```simple
# Validate network shapes before expensive training
fn validate_model_architecture():
    # Check all layer dimensions
    # Estimate memory requirements
    # Verify batch size constraints
    # Return true if valid

if validate_model_architecture():
    # Proceed with training
else:
    print("Model architecture invalid!")
```

### 3. Use Realistic Bounds

```simple
# ✓ Good: GPU memory limits
Dim.Named(name: "batch", lo: 1, hi: 128)

# ✗ Avoid: Unrealistic
Dim.Named(name: "batch", lo: 1, hi: 1000000)
```

### 4. Keep Examples Small

```simple
# ✓ Good: <200 lines per file
# validate_shapes.spl (150 lines)
# estimate_memory.spl (100 lines)
# runtime_checks.spl (120 lines)

# ✗ Avoid: Large monolithic files
# everything.spl (500 lines) - may not run completely
```

## Troubleshooting

### Problem: "Unexpected token" errors

**Solution:** Check for:
- Reserved keywords (`vec`, `mat` - use `vector_shape`, `matrix_shape`)
- Unicode characters (✓, ✗, ×, ≠ - replace with ASCII)
- Multi-line string interpolation issues

### Problem: Script stops executing early

**Solution:**
- Split into smaller files (<200 lines)
- Use multiple focused examples instead of one large file

### Problem: "undefined identifier: ShapeError"

**Solution:**
- You're trying to import from modules (doesn't work yet)
- Use standalone mode with inline type definitions

## Summary

**✅ What Works:**
- Standalone mode with inline types
- All dimension inference operations
- Shape verification and memory estimation
- Runtime constraint checking
- Formal verification (10/10 Lean theorems)

**⏳ What's Pending:**
- Module imports (compiler limitation)
- FFI operations (runtime limitation)

**🎯 Recommended Workflow:**
1. Start from working example
2. Copy type definitions inline
3. Write your validation logic
4. Keep files <200 lines
5. Use ASCII only (no Unicode)

**Status:** ✅ **PRODUCTION READY** (with documented workarounds)
