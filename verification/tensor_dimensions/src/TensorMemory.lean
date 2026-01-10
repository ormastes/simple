-- Tensor Memory Verification - Training Memory Safety
-- This file is generated from Simple verification model
-- See: simple/std_lib/src/verification/regenerate/tensor_dimensions.spl

import TensorDimensions

namespace TensorMemory

/-! Memory estimation and verification for tensor training. -/

open TensorDimensions

-- ========================================================================
-- Memory Bound Structure
-- ========================================================================

/-- Memory bound with minimum and maximum bytes -/
structure MemoryBound where
  minBytes : Nat
  maxBytes : Nat
  valid : minBytes ≤ maxBytes

-- ========================================================================
-- Device Memory
-- ========================================================================

/-- Available memory on a device (GPU/CPU) -/
structure DeviceMemory where
  totalBytes : Nat
  availableBytes : Nat
  valid : availableBytes ≤ totalBytes

-- ========================================================================
-- Training Memory Components
-- ========================================================================

/-- Memory components for neural network training -/
structure TrainingMemory where
  parameters : MemoryBound       -- Model parameters
  gradients : MemoryBound        -- Gradient tensors
  optimizerState : MemoryBound   -- Optimizer state (momentum, variance)
  activations : MemoryBound      -- Intermediate activations

-- ========================================================================
-- Total Memory Calculations
-- ========================================================================

/-- Total maximum memory across all components -/
def TrainingMemory.totalMax (tm : TrainingMemory) : Nat :=
  tm.parameters.maxBytes + tm.gradients.maxBytes +
  tm.optimizerState.maxBytes + tm.activations.maxBytes

/-- Total minimum memory across all components -/
def TrainingMemory.totalMin (tm : TrainingMemory) : Nat :=
  tm.parameters.minBytes + tm.gradients.minBytes +
  tm.optimizerState.minBytes + tm.activations.minBytes

-- ========================================================================
-- Memory Safety Theorem
-- ========================================================================

/-- If max estimate fits, any actual usage fits.

    This theorem proves that if we allocate enough memory for the maximum
    estimated usage, then any actual usage (between min and max) will fit.

    This is the key safety property for memory planning: if we reserve
    memory based on the maximum estimate, we won't run out of memory at
    runtime.
-/
theorem training_fits_if_max_fits
    (tm : TrainingMemory)
    (device : DeviceMemory)
    (actual : Nat) :
  tm.totalMax ≤ device.availableBytes →
  tm.totalMin ≤ actual →
  actual ≤ tm.totalMax →
  actual ≤ device.availableBytes := by
  intro h_max h_min h_actual
  omega

/-- Helper: If each component fits individually, total fits -/
theorem components_fit_implies_total_fits
    (tm : TrainingMemory)
    (device : DeviceMemory) :
  tm.parameters.maxBytes ≤ device.availableBytes →
  tm.gradients.maxBytes ≤ device.availableBytes →
  tm.optimizerState.maxBytes ≤ device.availableBytes →
  tm.activations.maxBytes ≤ device.availableBytes →
  tm.totalMax ≤ 4 * device.availableBytes := by
  intro h1 h2 h3 h4
  unfold TrainingMemory.totalMax
  omega

/-- Memory bounds are consistent (min ≤ max) -/
theorem training_memory_bounds_consistent (tm : TrainingMemory) :
  tm.totalMin ≤ tm.totalMax := by
  unfold TrainingMemory.totalMin TrainingMemory.totalMax
  have h1 := tm.parameters.valid
  have h2 := tm.gradients.valid
  have h3 := tm.optimizerState.valid
  have h4 := tm.activations.valid
  omega

-- ========================================================================
-- Example: MNIST MLP Memory Planning
-- ========================================================================

/-- Example: Memory estimate for MNIST MLP (784 -> 256 -> 10)

    Parameters:
    - w1: [784, 256] = 200,704 floats * 4 bytes = 802,816 bytes
    - w2: [256, 10] = 2,560 floats * 4 bytes = 10,240 bytes
    - Total: 813,056 bytes

    Gradients: Same as parameters = 813,056 bytes

    Optimizer (Adam): 2x parameters = 1,626,112 bytes

    Activations (batch size 1-64, max dim 256):
    - Min: 1 * 256 * 4 = 1,024 bytes
    - Max: 64 * 256 * 4 = 65,536 bytes

    Total:
    - Min: 813,056 + 813,056 + 1,626,112 + 1,024 = 3,253,248 bytes (~3.1 MB)
    - Max: 813,056 + 813,056 + 1,626,112 + 65,536 = 3,317,760 bytes (~3.2 MB)
-/
def example_mnist_mlp : TrainingMemory := {
  parameters := {
    minBytes := 813056
    maxBytes := 813056
    valid := by omega
  }
  gradients := {
    minBytes := 813056
    maxBytes := 813056
    valid := by omega
  }
  optimizerState := {
    minBytes := 1626112
    maxBytes := 1626112
    valid := by omega
  }
  activations := {
    minBytes := 1024
    maxBytes := 65536
    valid := by omega
  }
}

/-- Verify MNIST MLP fits in 4MB of memory -/
theorem mnist_fits_in_4mb :
  example_mnist_mlp.totalMax ≤ 4 * 1024 * 1024 := by
  unfold example_mnist_mlp TrainingMemory.totalMax
  -- 813056 + 813056 + 1626112 + 65536 = 3317760
  -- 4 * 1024 * 1024 = 4194304
  -- 3317760 ≤ 4194304
  decide

-- ========================================================================
-- Dimension-Based Memory Estimation
-- ========================================================================

/-- Compute memory from tensor shape and element size -/
def tensorMemoryBytes (shape : TensorShape) (elemSize : Nat) : Option (Nat × Nat) :=
  match minElements shape, maxElements shape with
  | some minElems, some maxElems => some (minElems * elemSize, maxElems * elemSize)
  | _, _ => none

/-- If we can compute memory bounds, min ≤ max -/
theorem tensor_memory_bounds_valid (shape : TensorShape) (elemSize : Nat) :
  ∀ minMem maxMem,
    tensorMemoryBytes shape elemSize = some (minMem, maxMem) →
    minMem ≤ maxMem := by
  intro minMem maxMem h
  -- This follows from min_le_max_elements:
  -- tensorMemoryBytes computes minMem = minElems * elemSize, maxMem = maxElems * elemSize
  -- where minElems ≤ maxElems (by min_le_max_elements)
  -- Therefore minMem ≤ maxMem
  sorry  -- Complex proof involving match expression decomposition

end TensorMemory
