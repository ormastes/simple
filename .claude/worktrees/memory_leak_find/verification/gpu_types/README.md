# GPU Types - Lean 4 Verification

Formal verification of Simple's GPU type system using Lean 4.

## Overview

This project proves key safety and correctness properties of the GPU type system, including:

- **Device Safety**: Values from different devices cannot be mixed
- **Transfer Correctness**: Device transfers preserve values
- **Type Inference**: `@gpu(device)` annotations work correctly

## Project Structure

```
verification/gpu_types/
├── lakefile.lean          # Lean project configuration
├── GpuTypes.lean          # Main module (imports all)
└── GpuTypes/
    ├── Basic.lean         # Core type definitions
    ├── Safety.lean        # Device safety proofs
    └── Inference.lean     # Type inference proofs
```

## Type System Model

### Device Enumeration

```lean
inductive Device where
  | Primary : Device
  | Secondary : Device
  | Inference : Device
  | Backup : Device
```

### GPU Type

```lean
structure Gpu (α : Type) (d : Device) where
  value : α
  device : Device
  device_eq : device = d
```

### GPU Function

```lean
structure GpuFunction (d : Device) (α β : Type) where
  impl : α → β
  device : Device
  device_eq : device = d
```

## Key Theorems

### Safety Theorems (GpuTypes/Safety.lean)

1. **Device Tracking**: `device_tracking_correct`
   ```lean
   theorem device_tracking_correct {α : Type} {d : Device} (x : Gpu α d) :
     Gpu.deviceOf x = d
   ```

2. **No Device Mixing**: `no_device_mixing`
   ```lean
   theorem no_device_mixing {α : Type}
       (x : Gpu α Primary) (y : Gpu α Secondary) :
     Gpu.deviceOf x ≠ Gpu.deviceOf y
   ```

3. **Transfer Type Safety**: `transfer_type_safe`
   ```lean
   theorem transfer_type_safe {α : Type} {d1 d2 : Device} (x : Gpu α d1) :
     Gpu.deviceOf (Gpu.transfer d2 x) = d2
   ```

4. **Value Preservation**: `transfer_value_preservation`
   ```lean
   theorem transfer_value_preservation {α : Type} {d1 d2 : Device}
       (x : Gpu α d1) :
     (Gpu.transfer d2 x).get = x.get
   ```

### Inference Theorems (GpuTypes/Inference.lean)

1. **Annotation Returns GPU Type**: `annotated_function_returns_gpu`
   ```lean
   theorem annotated_function_returns_gpu {d : Device} {α β : Type}
       (f : GpuFunction d α β) (x : α) :
     ∃ (result : Gpu β d), result.value = f.impl x
   ```

2. **Device Matching**: `inferred_device_matches`
   ```lean
   theorem inferred_device_matches {d : Device} {α β : Type}
       (f : GpuFunction d α β) (x : α) :
     (f.apply x).device = d
   ```

3. **Inference Correctness**: `inference_correct`
   ```lean
   theorem inference_correct {d : Device} {α β : Type}
       (f : GpuFunction d α β) :
     f.device = d
   ```

4. **Auto-unwrap Safety**: `auto_unwrap_safe`
   ```lean
   theorem auto_unwrap_safe {d : Device} {α : Type} (x : Gpu α d) :
     ∃ (v : α), v = x.get
   ```

5. **Operations Preserve Device**: `binary_op_preserves_device`
   ```lean
   theorem binary_op_preserves_device {d : Device} {α : Type}
       (op : BinaryOp α) (x y : Gpu α d) :
     (gpu_binary_op op x y).device = d
   ```

## Building

### Prerequisites

- Lean 4 (version 4.0.0 or later)
- Lake (Lean build tool)

### Build Instructions

```bash
# Navigate to project directory
cd verification/gpu_types

# Build project
lake build

# Expected output:
# Building GpuTypes.Basic
# Building GpuTypes.Safety
# Building GpuTypes.Inference
# Building GpuTypes
```

### Verification

All theorems should verify successfully. If any theorem fails to verify, it indicates a problem with the type system design.

## Correspondence with Simple

### Simple Code

```simple
enum UserGpu:
    Primary
    Secondary

@gpu(Primary)
fn compute(x: Int) -> Int:
    x + 1

let result = compute(42)  # Type: Gpu[Int, Primary]
```

### Lean Model

```lean
-- Define function
def compute_impl (x : Nat) : Nat := x + 1

def compute : GpuFunction Primary Nat Nat :=
  { impl := compute_impl
    device := Primary
    device_eq := rfl }

-- Apply function
def result := compute.apply 42

-- Verify type
#check result  -- result : Gpu Nat Primary
```

## Theorem Implications

### Safety Guarantees

1. **No Device Mixing**: Impossible to accidentally use a value from GPU 1 in a computation on GPU 0
2. **Type-Safe Transfers**: Compiler tracks which device each value is on
3. **Correct Inference**: `@gpu(Primary)` always produces `Gpu[T, Primary]`

### Performance Implications

1. **Zero Runtime Cost**: All device tracking is compile-time only
2. **No Runtime Checks**: Type system eliminates need for runtime device validation
3. **Optimal Transfers**: Compiler can optimize transfer sequences

## Future Work

1. **Memory Safety**: Prove that GPU memory is properly managed
2. **Concurrency**: Prove that concurrent GPU operations are safe
3. **Optimization**: Prove correctness of transfer elimination optimizations
4. **Multi-GPU**: Extend to multiple devices with peer-to-peer transfers

## References

- [Simple Language Documentation](../../doc/README.md)
- [GPU Type Design](../../doc/design/simplified_gpu_types.md)
- [Lean 4 Documentation](https://lean-lang.org/)

---

**Status**: ✅ All theorems verified
**Date**: 2026-01-10
**Lean Version**: 4.0.0
