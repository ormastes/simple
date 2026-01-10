# Tensor Dimension Inference - Lean 4 Verification

Formal verification of tensor dimension inference correctness using Lean 4.

## Overview

This project contains Lean 4 proofs for the tensor dimension inference system implemented in Simple. The Lean code is automatically generated from the Simple verification model.

## Generated Files

- `src/TensorDimensions.lean` - Dimension types, unification, and shape inference
- `src/TensorMemory.lean` - Memory estimation and bounds verification

## Theorems

### TensorDimensions.lean

1. **`shapesCompatible_refl`** - Shape compatibility is reflexive
   ```lean
   theorem shapesCompatible_refl (s : TensorShape) :
     shapesCompatible s s = true
   ```

2. **`unifyDim_success_eq`** - Successful unification implies dimension equality
   ```lean
   theorem unifyDim_success_eq (d1 d2 d : Dim) :
     unifyDim d1 d2 = UnifyResult.success d → dimEq d1 d ∨ dimEq d2 d
   ```

3. **`matmulShape_deterministic`** - Matmul shape inference is deterministic
   ```lean
   theorem matmulShape_deterministic (l r s1 s2 : TensorShape) :
     matmulShape l r = some s1 → matmulShape l r = some s2 → s1 = s2
   ```

4. **`min_le_max_elements`** - Memory bounds are valid (min ≤ max)
   ```lean
   theorem min_le_max_elements (s : TensorShape) :
     ∀ min max, minElements s = some min → maxElements s = some max → min ≤ max
   ```

### TensorMemory.lean

1. **`training_fits_if_max_fits`** - Training memory safety
   ```lean
   theorem training_fits_if_max_fits (tm : TrainingMemory) (device : DeviceMemory) (actual : ℕ) :
     tm.totalMax ≤ device.availableBytes →
     tm.totalMin ≤ actual →
     actual ≤ tm.totalMax →
     actual ≤ device.availableBytes
   ```

## Generating Lean Code

The Lean files are generated from the Simple verification model:

```bash
# From simple project root
./target/debug/simple -c "
import verification.regenerate.tensor_dimensions as regen
let dims_code = regen.regenerate_tensor_dimensions()
let mem_code = regen.regenerate_tensor_memory()
# Write to files...
"
```

Or use the regeneration script:

```bash
# Run full regeneration (includes all 15 verification projects)
./target/debug/simple simple/std_lib/src/verification/regenerate/__init__.spl
```

## Building and Verifying

```bash
# Initialize Lake (first time only)
lake update

# Build the project
lake build

# Verify all theorems compile
lake exe verify
```

## What Gets Verified

1. **Dimension Unification**: Unification algorithm produces compatible dimensions
2. **Shape Inference**: Matrix multiplication shape inference is correct and deterministic
3. **Memory Bounds**: Element count estimation respects min ≤ max invariant
4. **Training Memory**: Maximum memory estimate is a safe upper bound

## Dependencies

- Lean 4 (stable toolchain)
- Lake (Lean build system)

## Status

- ✅ Lean code generation implemented
- ✅ Core theorems defined
- ⏳ Proof automation (some proofs use `sorry`)
- ⏳ Integration with CI/CD pipeline

## See Also

- [Design Documentation](../../doc/design/tensor_dimensions_design.md)
- [User Guide](../../doc/guide/tensor_dimensions_guide.md)
- [Simple Implementation](../../simple/std_lib/src/ml/torch/typed_tensor.spl)
- [Verification Model](../../simple/std_lib/src/verification/models/tensor_dimensions.spl)
