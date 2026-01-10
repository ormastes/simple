# Tensor Dimension Inference - Design Documentation

**Feature ID:** #193
**Status:** Implementing
**Author:** Simple Team
**Last Updated:** 2026-01-10

## Table of Contents

1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Dimension Representation](#dimension-representation)
4. [Unification Algorithm](#unification-algorithm)
5. [Shape Inference Rules](#shape-inference-rules)
6. [Type System Integration](#type-system-integration)
7. [Runtime Verification](#runtime-verification)
8. [Memory Estimation](#memory-estimation)
9. [Lean Verification](#lean-verification)
10. [Implementation Details](#implementation-details)
11. [Future Work](#future-work)

---

## Overview

Tensor dimension inference provides compile-time tracking of N-dimensional tensor shapes with optional range constraints. The system combines:

1. **Static Analysis**: Compile-time dimension inference using unification
2. **Runtime Verification**: Checking actual dimensions against declared constraints
3. **Memory Planning**: Computing memory bounds from dimension ranges
4. **Formal Verification**: Lean 4 proofs of correctness

### Design Goals

- **Type Safety**: Catch dimension mismatches at compile time
- **Flexibility**: Support both static and dynamic dimensions
- **Performance**: Minimal runtime overhead
- **Composability**: Integrate cleanly with existing type system
- **Verifiability**: Enable formal proofs of dimension inference correctness

### Non-Goals

- **Full Dependent Types**: Not implementing full dependent type system
- **Symbolic Dimensions**: Not supporting symbolic arithmetic on dimensions
- **Automatic Batching**: Not implementing automatic batch dimension insertion

---

## Architecture

### Module Structure

```
simple/std_lib/src/
├── ml/torch/
│   ├── typed_tensor.spl          # TypedTensor class & operations
│   ├── dtype.spl                 # Data type definitions
│   └── device.spl                # Device (CPU/GPU) definitions
├── verification/models/
│   └── tensor_dimensions.spl     # Core dimension inference model
└── verification/regenerate/
    └── tensor_dimensions.spl     # Lean code generator
```

### Component Layers

```
┌─────────────────────────────────────────┐
│   User Code (TypedTensor operations)   │
└──────────────┬──────────────────────────┘
               │
┌──────────────▼──────────────────────────┐
│  TypedTensor API (typed_tensor.spl)    │
│  - zeros, ones, randn                   │
│  - matmul, add, reshape, transpose      │
│  - verify, memory estimation            │
└──────────────┬──────────────────────────┘
               │
┌──────────────▼──────────────────────────┐
│  Dimension Inference                    │
│  (verification/models/tensor_dims.spl)  │
│  - Dimension types & unification        │
│  - Shape inference operations           │
│  - Runtime verification                 │
└──────────────┬──────────────────────────┘
               │
┌──────────────▼──────────────────────────┐
│  PyTorch FFI (tensor_ffi.spl)          │
│  - rt_torch_zeros, rt_torch_matmul     │
│  - rt_torch_shape, rt_torch_reshape    │
└─────────────────────────────────────────┘
```

### Data Flow

1. **Creation**: User creates `TypedTensor` with `DimSpec` constraints
2. **Inference**: Operations infer output shape using unification
3. **Execution**: PyTorch FFI performs actual computation
4. **Verification**: Runtime checks actual shape against constraints

---

## Dimension Representation

### Dimension Type Hierarchy

```simple
enum Dim:
    Literal(value: Int)                              # Fixed: 64
    Var(var: DimVar)                                 # Inference variable: α
    Named(name: String, range: Option[(Int, Int)])   # Named: batch: 1..64
    Dynamic                                          # Runtime-only: *
    Broadcast                                        # Can be 1 or match: ?
```

### Dimension Semantics

#### Literal
**Representation**: `Dim.Literal(value: 64)`

**Meaning**: Dimension is exactly `value` at compile time and runtime.

**Unification**:
- `Literal(n)` ⊔ `Literal(n)` = `Literal(n)`
- `Literal(n)` ⊔ `Literal(m)` = ⊥ (if n ≠ m)

**Example**: Image width always 224

#### Variable
**Representation**: `Dim.Var(var: DimVar { id: 0, name: Some("α") })`

**Meaning**: Unknown dimension to be inferred (like type variable in type inference).

**Unification**:
- `Var(α)` ⊔ `d` = `d` (bind α to d)
- `Var(α)` ⊔ `Var(β)` = `Var(α)` (arbitrary choice, union-find)

**Example**: Intermediate shape in inference

#### Named
**Representation**: `Dim.Named(name: "batch", range: Some((1, 64)))`

**Meaning**: Dimension has semantic name and optional runtime range constraint.

**Unification**:
- `Named(n, r1)` ⊔ `Named(n, r2)` = `Named(n, r1 ∩ r2)` (same name, intersect ranges)
- `Named(n, r)` ⊔ `Literal(v)` = `Literal(v)` (if v ∈ r, else ⊥)

**Example**: Batch size varies between 1 and 64

#### Dynamic
**Representation**: `Dim.Dynamic`

**Meaning**: Fully dynamic dimension with no compile-time constraints.

**Unification**:
- `Dynamic` ⊔ `d` = `d` (matches anything)

**Example**: Unknown dimension from external data

#### Broadcast
**Representation**: `Dim.Broadcast`

**Meaning**: Dimension is 1 or matches another dimension (NumPy broadcasting).

**Unification**:
- `Broadcast` ⊔ `Literal(1)` = `Literal(1)`
- `Broadcast` ⊔ `Literal(n)` = `Literal(n)` (n > 1)
- `Broadcast` ⊔ `Broadcast` = `Broadcast`

**Example**: Bias vector broadcasting over batch dimension

### DimSpec (User-Facing API)

```simple
class DimSpec:
    name: Option<String>
    sample: Int
    min_val: Option<Int>
    max_val: Option<Int>
```

**Conversion to Dim**:
- Exact: `DimSpec(None, 64, Some(64), Some(64))` → `Dim.Literal(64)`
- Named: `DimSpec(Some("batch"), 32, None, None)` → `Dim.Named("batch", None)`
- Ranged: `DimSpec(Some("batch"), 32, Some(1), Some(64))` → `Dim.Named("batch", Some((1, 64)))`
- Dynamic: `DimSpec(None, 1, None, None)` → `Dim.Dynamic`

---

## Unification Algorithm

### Algorithm W for Dimensions

The dimension inference algorithm is based on Algorithm W (Hindley-Milner type inference):

```
unify_dims(ctx: DimInferenceContext, d1: Dim, d2: Dim) -> Result<Dim, ShapeError>:
    match (d1, d2):
        # Reflexivity
        case (Literal(n), Literal(n)):
            return Ok(Literal(n))

        # Contradiction
        case (Literal(n), Literal(m)) if n ≠ m:
            return Err(LiteralMismatch(n, m))

        # Variable binding
        case (Var(α), d):
            ctx.bind(α, d)
            return Ok(d)
        case (d, Var(α)):
            ctx.bind(α, d)
            return Ok(d)

        # Dynamic matches anything
        case (Dynamic, d) | (d, Dynamic):
            return Ok(d)

        # Broadcast rules
        case (Broadcast, Literal(1)) | (Literal(1), Broadcast):
            return Ok(Literal(1))
        case (Broadcast, Literal(n)) | (Literal(n), Broadcast):
            return Ok(Literal(n))
        case (Broadcast, Broadcast):
            return Ok(Broadcast)

        # Named dimensions
        case (Named(n1, r1), Named(n2, r2)) if n1 == n2:
            let r = intersect_ranges(r1, r2)
            if r.is_empty():
                return Err(RangeEmpty(n1, r1, r2))
            return Ok(Named(n1, r))

        # Named + Literal
        case (Named(n, Some((lo, hi))), Literal(v)):
            if lo <= v <= hi:
                return Ok(Literal(v))
            else:
                return Err(OutOfRange(n, v, lo, hi))

        # Default: incompatible
        case _:
            return Err(Incompatible(d1, d2))
```

### Inference Context

```simple
class DimInferenceContext:
    next_var_id: mut Int
    bindings: mut Dict[DimVar, Dim]

    fn fresh_var(self) -> Dim.Var:
        let id = self.next_var_id
        self.next_var_id += 1
        return Dim.Var(DimVar { id: id, name: None })

    fn bind(self, var: DimVar, dim: Dim):
        self.bindings[var] = dim

    fn resolve(self, dim: Dim) -> Dim:
        match dim:
            case Var(v):
                match self.bindings.get(v):
                    case Some(d): return self.resolve(d)
                    case None: return dim
            case _:
                return dim
```

### Shape Unification

```simple
unify_shapes(ctx: DimInferenceContext, s1: TensorShape, s2: TensorShape)
    -> Result<TensorShape, ShapeError>:

    if s1.ndim() != s2.ndim():
        return Err(RankMismatch(s1, s2))

    let mut unified = []
    for (d1, d2) in zip(s1.dims, s2.dims):
        unified.push(unify_dims(ctx, d1, d2)?)

    return Ok(TensorShape(dims: unified))
```

---

## Shape Inference Rules

### Matrix Multiplication

**Rule**: `[M, K] @ [K, N] → [M, N]`

**Algorithm**:
```simple
infer_matmul_shape(ctx, left: TensorShape, right: TensorShape)
    -> Result<TensorShape, ShapeError>:

    if left.ndim() != 2 or right.ndim() != 2:
        return Err(MatmulRankError(left, right))

    let [m, k1] = left.dims
    let [k2, n] = right.dims

    let k = unify_dims(ctx, k1, k2)?  # K dimensions must match

    return Ok(TensorShape(dims: [m, n]))
```

**Example**:
```
[4, 8] @ [8, 16] → [4, 16]
[4, α] @ [8, 16] → bind α = 8, result [4, 16]
[4, 8] @ [10, 16] → Error: K mismatch (8 vs 10)
```

### Broadcasting

**Rule**: NumPy broadcasting semantics

**Algorithm**:
```simple
infer_broadcast_shape(ctx, shapes: List<TensorShape>)
    -> Result<TensorShape, ShapeError>:

    # Align shapes to same rank (pad left with 1)
    let max_rank = max(s.ndim() for s in shapes)
    let aligned = shapes.map(|s| s.pad_left(max_rank))

    # Unify dimension-wise
    let mut result_dims = []
    for i in 0..max_rank:
        let dims_at_i = aligned.map(|s| s.dims[i])
        result_dims.push(unify_broadcast_dims(ctx, dims_at_i)?)

    return Ok(TensorShape(dims: result_dims))

unify_broadcast_dims(ctx, dims: List<Dim>) -> Result<Dim, ShapeError>:
    # Find non-1 dimension
    let mut non_one = None
    for d in dims:
        match d:
            case Literal(1): continue
            case _:
                match non_one:
                    case None:
                        non_one = Some(d)
                    case Some(d2):
                        let unified = unify_dims(ctx, d, d2)?
                        non_one = Some(unified)

    return Ok(non_one.unwrap_or(Literal(1)))
```

**Example**:
```
[3, 4] + [1, 4] → [3, 4]
[3, 4] + [3, 1] → [3, 4]
[2, 3, 4] + [4] → [2, 3, 4]
[3, 4] + [5, 4] → Error: 3 vs 5 in first dim
```

### Reshape

**Rule**: Element count must be preserved

**Algorithm**:
```simple
verify_reshape(ctx, input_shape: TensorShape, output_shape: TensorShape)
    -> Result<(), ShapeError>:

    let input_elems = compute_product(input_shape.dims)?
    let output_elems = compute_product(output_shape.dims)?

    if input_elems != output_elems:
        return Err(ReshapeElementsMismatch(input_shape, output_shape))

    return Ok(())

compute_product(dims: List<Dim>) -> Result<Int, ShapeError>:
    let mut product = 1
    for d in dims:
        match d:
            case Literal(n):
                product *= n
            case _:
                return Err(CannotComputeProduct(dims))
    return Ok(product)
```

**Example**:
```
[4, 6] → [2, 12]  ✓ (24 elements both)
[4, 6] → [3, 10]  ✗ (24 vs 30)
[batch, 6] → [batch, 3, 2]  ? (need runtime check)
```

### Transpose

**Rule**: Swap two dimensions

**Algorithm**:
```simple
infer_transpose_shape(shape: TensorShape, dim0: Int, dim1: Int)
    -> Result<TensorShape, ShapeError>:

    if dim0 < 0 or dim0 >= shape.ndim() or dim1 < 0 or dim1 >= shape.ndim():
        return Err(InvalidTransposeDims(dim0, dim1, shape.ndim()))

    let mut new_dims = shape.dims.clone()
    swap(&mut new_dims[dim0], &mut new_dims[dim1])

    return Ok(TensorShape(dims: new_dims))
```

### Reduction

**Rule**: Reduce along dimension (optionally keep dim as 1)

**Algorithm**:
```simple
infer_reduction_shape(shape: TensorShape, dim: Int, keepdim: Bool)
    -> Result<TensorShape, ShapeError>:

    if dim < 0 or dim >= shape.ndim():
        return Err(InvalidReductionDim(dim, shape.ndim()))

    let mut new_dims = []
    for (i, d) in shape.dims.enumerate():
        if i == dim:
            if keepdim:
                new_dims.push(Literal(1))
        else:
            new_dims.push(d)

    return Ok(TensorShape(dims: new_dims))
```

---

## Type System Integration

### TensorType

```simple
class TensorType:
    shape: TensorShape
    dtype: DType

TensorShape:
    dims: List<Dim>
```

### TypedTensor

```simple
class TypedTensor:
    handle: u64              # PyTorch tensor handle
    tensor_type: TensorType  # Type-level shape + dtype
```

**Invariant**: `actual_shape()` must satisfy constraints in `tensor_type.shape`

### Operation Typing

Each operation has a type signature:

```simple
matmul: (TypedTensor[S1], TypedTensor[S2]) → Result<TypedTensor[S3], ShapeError>
  where S1 = [M, K], S2 = [K, N], S3 = [M, N]

add: (TypedTensor[S1], TypedTensor[S2]) → Result<TypedTensor[S3], ShapeError>
  where S3 = broadcast(S1, S2)

reshape: (TypedTensor[S1], TargetShape[S2]) → Result<TypedTensor[S2], ShapeError>
  where product(S1) = product(S2)
```

---

## Runtime Verification

### Verification Points

1. **Tensor Creation**: Check actual shape matches `DimSpec` constraints
2. **Operation Results**: Check output shape satisfies inferred constraints
3. **Explicit Verify**: User calls `.verify()` method

### Verification Algorithm

```simple
verify_shape_at_runtime(actual: List<Int>, declared: TensorShape)
    -> Result<(), ShapeError>:

    if actual.len() != declared.dims.len():
        return Err(RankMismatch(actual.len(), declared.dims.len()))

    for (actual_dim, declared_dim) in zip(actual, declared.dims):
        verify_dim_at_runtime(actual_dim, declared_dim)?

    return Ok(())

verify_dim_at_runtime(actual: Int, declared: Dim) -> Result<(), ShapeError>:
    match declared:
        case Literal(expected):
            if actual != expected:
                return Err(DimMismatch(actual, expected))

        case Named(name, Some((lo, hi))):
            if actual < lo or actual > hi:
                return Err(OutOfRange(name, actual, lo, hi))

        case _:
            # Dynamic, Var, Named without range: accept any

    return Ok(())
```

### Performance Considerations

- Verification is O(ndim), typically < 10 dimensions
- Skip verification for `Dim.Dynamic` and `Dim.Var`
- Cache verification results (future optimization)

---

## Memory Estimation

### Estimation Algorithm

```simple
estimate_tensor_memory(shape: TensorShape, elem_size: Int) -> (Int, Int):
    let (min_elems, max_elems) = estimate_element_range(shape)
    return (min_elems * elem_size, max_elems * elem_size)

estimate_element_range(shape: TensorShape) -> (Int, Int):
    let mut min_product = 1
    let mut max_product = 1

    for dim in shape.dims:
        match dim:
            case Literal(n):
                min_product *= n
                max_product *= n

            case Named(_, Some((lo, hi))):
                min_product *= lo
                max_product *= hi

            case Named(_, None):
                # Use sample value (requires DimSpec context)
                min_product *= 1
                max_product *= LARGE_VALUE

            case Dynamic:
                min_product *= 1
                max_product *= LARGE_VALUE

            case _:
                # Var, Broadcast: assume 1
                min_product *= 1
                max_product *= 1

    return (min_product, max_product)
```

### Training Memory Model

```simple
training_memory = parameters + gradients + optimizer_state + activations

parameters: Fixed (model architecture)
gradients: Same as parameters
optimizer_state: 2x parameters (Adam: momentum + variance)
activations: Varies with batch size
```

**Example**:
```simple
# Parameters: [784, 256] + [256, 10] = 200,960 + 2,560 = 203,520 floats
param_mem = 203,520 * 4 = 814,080 bytes

# Gradients: Same as parameters
grad_mem = 814,080 bytes

# Optimizer state: 2x parameters (Adam)
opt_mem = 2 * 814,080 = 1,628,160 bytes

# Activations: batch_size * max_activation_dim
# batch in [1, 64], max activation = 256
act_mem_min = 1 * 256 * 4 = 1,024 bytes
act_mem_max = 64 * 256 * 4 = 65,536 bytes

# Total
total_min = 814,080 + 814,080 + 1,628,160 + 1,024 = 3,257,344 bytes (3.1 MB)
total_max = 814,080 + 814,080 + 1,628,160 + 65,536 = 3,321,856 bytes (3.2 MB)
```

---

## Lean Verification

### Generated Lean Code

The system generates Lean 4 code for formal verification:

```lean
-- verification/tensor_dimensions/src/TensorDimensions.lean

inductive Dim where
  | literal (value : Nat)
  | variable (id : Nat) (name : Option String)
  | named (name : String) (lo hi : Option Nat)
  | dynamic
  | broadcast

abbrev TensorShape := List Dim

def unifyDim : Dim → Dim → UnifyResult := ...

def matmulShape (left right : TensorShape) : Option TensorShape := ...
```

### Theorems

**Reflexivity**:
```lean
theorem shapesCompatible_refl (s : TensorShape) :
  shapesCompatible s s = true := by
  induction s with
  | nil => rfl
  | cons d s' ih => simp [shapesCompatible, dimEq]; exact ih
```

**Unification Correctness**:
```lean
theorem unifyDim_success_eq (d1 d2 d : Dim) :
  unifyDim d1 d2 = UnifyResult.success d → dimEq d1 d ∨ dimEq d2 d := ...
```

**Matmul Determinism**:
```lean
theorem matmulShape_deterministic (l r s1 s2 : TensorShape) :
  matmulShape l r = some s1 → matmulShape l r = some s2 → s1 = s2 := ...
```

**Memory Bounds**:
```lean
theorem min_le_max_elements (s : TensorShape) :
  ∀ min max, minElements s = some min → maxElements s = some max → min ≤ max := ...
```

**Training Memory Safety**:
```lean
theorem training_fits_if_max_fits (tm : TrainingMemory) (device : DeviceMemory) (actual : Nat) :
  tm.totalMax ≤ device.availableBytes →
  tm.totalMin ≤ actual →
  actual ≤ tm.totalMax →
  actual ≤ device.availableBytes := by omega
```

### Verification Workflow

```bash
# Generate Lean files
simple gen-lean generate --project tensor_dimensions

# Build Lean project
cd verification/tensor_dimensions
lake build

# Verify theorems
lake exe verify
```

---

## Implementation Details

### File Structure

**`typed_tensor.spl`** (~350 LOC):
- `DimSpec` class (user-facing API)
- `TensorType` class (shape + dtype)
- `TypedTensor` class (operations)
- Factory methods: `zeros`, `ones`, `randn`
- Operations: `matmul`, `add`, `reshape`, `transpose`, `sum`, `mean`
- Memory estimation: `MemoryReport`

**`tensor_dimensions.spl`** (~450 LOC):
- `Dim` enum (dimension types)
- `DimVar` struct (variable metadata)
- `TensorShape` struct (list of dimensions)
- `DimInferenceContext` class (unification context)
- `ShapeError` enum (error types)
- Unification: `unify_dims`, `unify_shapes`
- Inference: `infer_matmul_shape`, `infer_broadcast_shape`, `verify_reshape`
- Verification: `verify_shape_at_runtime`, `verify_dim_at_runtime`
- Memory: `estimate_tensor_memory`, `estimate_element_range`

**`tensor_dimensions.spl` (regenerate)** (~200 LOC):
- Lean code generator
- `regenerate_tensor_dimensions()` - Generates `TensorDimensions.lean`
- `regenerate_tensor_memory()` - Generates `TensorMemory.lean`

### Key Data Structures

```simple
# Dimension variable (for unification)
struct DimVar:
    id: Int
    name: Option<String>

# Dimension inference context
class DimInferenceContext:
    next_var_id: mut Int
    bindings: mut Dict[DimVar, Dim]

# Tensor shape
struct TensorShape:
    dims: List<Dim>

# Shape error
enum ShapeError:
    LiteralMismatch(expected: Int, actual: Int)
    RankMismatch(left: TensorShape, right: TensorShape)
    MatmulShapeMismatch(left: TensorShape, right: TensorShape)
    BroadcastIncompatible(shapes: List<TensorShape>)
    ReshapeElementsMismatch(input: TensorShape, output: TensorShape)
    DimensionOutOfRange(name: String, actual: Int, min: Int, max: Int)
    InferenceError(message: String)
```

---

## Future Work

### Short Term

1. **Symbolic Dimensions**: Support `batch * 2`, `seq_len // 8` expressions
2. **Automatic Batching**: Insert batch dimensions automatically
3. **Einsum Notation**: Support Einstein summation notation for tensor operations
4. **Shape Polymorphism**: Generic functions over shapes

### Medium Term

1. **Static Analysis Pass**: Whole-program dimension inference
2. **Constraint Solver**: More sophisticated range constraint solving
3. **Performance Optimization**: Cache verification results
4. **Error Messages**: Better error messages with shape visualization

### Long Term

1. **Dependent Types**: Full dependent type system for dimensions
2. **Proof-Carrying Code**: Embed Lean proofs in compiled binaries
3. **Auto-Tuning**: Use dimension info for kernel selection
4. **Distributed Tensors**: Dimension tracking for sharded tensors

---

## References

1. **Type Inference**: Damas, L., & Milner, R. (1982). Principal type-schemes for functional programs.
2. **Dependent Types**: Brady, E. (2013). Idris, a general-purpose dependently typed programming language.
3. **Tensor Types**: Slepak, J. et al. (2014). An array-oriented language with static rank polymorphism.
4. **Lean 4**: de Moura, L., & Ullrich, S. (2021). The Lean 4 Theorem Prover and Programming Language.
5. **PyTorch Typing**: Li, Y. et al. (2020). Static Shape Inference for PyTorch Programs.

---

**Last Updated:** 2026-01-10
**Status:** Implementing
