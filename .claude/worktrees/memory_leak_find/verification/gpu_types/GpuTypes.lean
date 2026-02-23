/-
  GPU Types - Main Module

  Formal verification of GPU type system for Simple language.

  Proves:
  1. Device safety - no device mixing
  2. Transfer correctness - transfers preserve values
  3. Inference correctness - @gpu annotations work correctly
-/

import GpuTypes.Basic
import GpuTypes.Safety
import GpuTypes.Inference

/-!
# GPU Type System Verification

This module proves key properties of Simple's GPU type system.

## Type System Overview

The GPU type system uses type-level device parameters to track which
GPU a value resides on:

```lean
Gpu α d  -- Value of type α on device d
```

Functions are annotated with devices:

```simple
@gpu(Primary)
fn compute(x: Int) -> Int:
    x + 1  -- Returns Gpu[Int, Primary]
```

## Theorems Proved

### Safety (GpuTypes.Safety)

1. **Device Tracking**: Runtime device matches type-level device
2. **No Mixing**: Cannot mix values from different devices
3. **Transfer Safety**: Transfers are type-safe
4. **Value Preservation**: Transfers don't change values

### Inference (GpuTypes.Inference)

1. **Annotation Correctness**: @gpu(d) produces Gpu[T, d]
2. **Determinism**: Inference is deterministic
3. **Auto-unwrap**: Safe to unwrap in same device context
4. **Operations**: Binary ops preserve device

## Usage

To check these proofs:

```bash
cd verification/gpu_types
lake build
```

All theorems should verify successfully.
-/

namespace GpuVerification

-- Re-export key types
export Device (Primary Secondary Inference Backup)
export Gpu (make get transfer deviceOf)
export GpuFunction (apply)

-- Re-export key theorems
export GpuSafety (
  device_tracking_correct
  no_device_mixing
  transfer_type_safe
  transfer_value_preservation
)

export GpuInference (
  annotated_function_returns_gpu
  inferred_device_matches
  inference_correct
  auto_unwrap_safe
  auto_wrap_safe
  binary_op_preserves_device
)

end GpuVerification
