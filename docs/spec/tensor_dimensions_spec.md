# Tensor Dimension Inference

*Source: `simple/std_lib/test/features/data_structures/tensor_dimensions_spec.spl`*

---

# Tensor Dimension Inference

**Status:** Implementing
**Feature ID:** #193
**Keywords:** tensors, dimensions, shape, inference, types, verification
**Topics:** data-structures, type-system, machine-learning, formal-verification

## Overview

Tensor dimension inference provides compile-time tracking of N-dimensional tensor shapes
with optional range constraints. This enables:

1. **Static Shape Inference** - Shape propagation through operations (matmul, reshape, broadcast)
2. **Runtime Verification** - Checking actual dimensions satisfy declared constraints
3. **Memory Estimation** - Computing min/max memory bounds from dimension constraints
4. **Formal Verification** - Lean 4 proofs of inference correctness

## Dimension Types

### Literal
Fixed dimension known at compile time:
    ```simple
DimSpec.exact(64)  # Exactly 64
```

### Named
Named dimension with optional range:
    ```simple
DimSpec.named("batch", 32)              # Samplevalue 32
DimSpec.ranged("batch", 32, 1, 128)     # 32 sample, range [1, 128]
```

### Dynamic
Runtime-only dimension (no compile-time constraint):
    ```simple
DimSpec.dynamic()
```

## Shape Inference Operations

### Matrix Multiplication
```simple
val a = TypedTensor.randn([DimSpec.exact(4), DimSpec.exact(8)])   # [4, 8]
val b = TypedTensor.randn([DimSpec.exact(8), DimSpec.exact(16)])  # [8, 16]
val c = a.matmul(b)?  # Infers [4, 16]
```

### Broadcasting
```simple
val a = TypedTensor.randn([DimSpec.exact(3), DimSpec.exact(4)])
val b = TypedTensor.randn([DimSpec.exact(1), DimSpec.exact(4)])
val c = a.add(b)?  # Broadcasts to [3, 4]
```

### Reshape
```simple
val t = TypedTensor.randn([DimSpec.exact(4), DimSpec.exact(6)])  # 24 elements
val r = t.reshape([DimSpec.exact(2), DimSpec.exact(12)])?       # Still 24
```

## Runtime Verification

Verify actual tensor dimensions match declared constraints:
    ```simple
val t = TypedTensor.randn([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(784)
])

# Check actual shape satisfies constraints
match t.verify():
    case Ok(_):
        print("Dimensions valid!")
    case Err(e):
        print("Shape error: {e}")
```

## Memory Estimation

Compute memory bounds from dimension constraints:
    ```simple
val tt = TensorType.new([
    DimSpec.ranged("batch", 32, 1, 64),
    DimSpec.exact(256)
], DType.Float32)

val min_mem = tt.min_memory_bytes()  # 1 * 256 * 4 = 1024 bytes
val max_mem = tt.max_memory_bytes()  # 64 * 256 * 4 = 65536 bytes
```

## Lean 4 Verification

Generate formal proofs of dimension inference:
    ```bash
simple gen-lean generate --project tensor_dimensions
```

Theorems proved:
    - `shapesCompatible_refl` - Shape compatibility is reflexive
- `unifyDim_success_eq` - Unification implies equality
- `matmulShape_deterministic` - Matmul inference is deterministic
- `min_le_max_elements` - Memory bounds are valid
- `training_fits_if_max_fits` - Training memory verification

## Related Specifications

- **Tensor Literals** (#192) - Creating tensors from literals
- **Type Inference** (#8-9) - Type inference system
- **Generics** (#32) - Generic type parameters
- **Option/Result** (#27) - Error handling for shape mismatches

## Implementation Status

✅ Dimension types (Literal, Named, Dynamic, Broadcast, Var)
✅ Unification algorithm for dimension inference
✅ Shape inference for matmul, broadcast, reshape
✅ Runtime verification
✅ Memory estimation
✅ Lean 4 proof generation
⏳ Integration tests
⏳ User guide documentation
⏳ Public API exposure

## Test Coverage

Comprehensive BDD tests in `test/unit/ml/torch/typed_tensor_spec.spl`:
    - Dimension unification (literals, variables, named, dynamic, broadcast)
- Shape inference (matmul, broadcast)
- TypedTensor operations (creation, arithmetic, reshape)
- Memory estimation
- Multi-dimensional inference (3D, 4D tensors)
- Chain of operations

Total: 50+ test cases covering all dimension types and operations
