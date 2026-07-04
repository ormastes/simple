namespace TensorMemory
-- Memory estimation and verification for tensor training.
structure MemoryBound where
  minBytes : Nat
  maxBytes : Nat

structure DeviceMemory where
  totalBytes : Nat
  availableBytes : Nat

structure TrainingMemory where
  parameterBytes : MemoryBound
  gradients : MemoryBound
  optimizerState : MemoryBound
  activations : MemoryBound

def TrainingMemory.totalMax (tm : TrainingMemory) : Nat :=
  tm.parameterBytes.maxBytes + tm.gradients.maxBytes +
  tm.optimizerState.maxBytes + tm.activations.maxBytes

def TrainingMemory.totalMin (tm : TrainingMemory) : Nat :=
  tm.parameterBytes.minBytes + tm.gradients.minBytes +
  tm.optimizerState.minBytes + tm.activations.minBytes

theorem training_total_min_le_max (tm : TrainingMemory)
    (hp : tm.parameterBytes.minBytes ≤ tm.parameterBytes.maxBytes)
    (hg : tm.gradients.minBytes ≤ tm.gradients.maxBytes)
    (ho : tm.optimizerState.minBytes ≤ tm.optimizerState.maxBytes)
    (ha : tm.activations.minBytes ≤ tm.activations.maxBytes) :
    tm.totalMin ≤ tm.totalMax := by
  unfold TrainingMemory.totalMin TrainingMemory.totalMax
  omega

-- If max estimate fits, any actual usage fits.
theorem training_fits_if_max_fits (tm : TrainingMemory) (device : DeviceMemory) (actual : Nat) :
  tm.totalMax ≤ device.availableBytes → tm.totalMin ≤ actual → actual ≤ tm.totalMax → actual ≤ device.availableBytes := by
  intro h_max h_min h_actual
  exact Nat.le_trans h_actual h_max

end TensorMemory
