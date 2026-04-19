namespace TensorMemory
-- Memory estimation and verification for tensor training.
open TensorDimensions

structure MemoryBound where
  minBytes : ℕ
  maxBytes : ℕ
  valid : minBytes ≤ maxBytes

structure DeviceMemory where
  totalBytes : ℕ
  availableBytes : ℕ
  valid : availableBytes ≤ totalBytes

structure TrainingMemory where
  parameters : MemoryBound
  gradients : MemoryBound
  optimizerState : MemoryBound
  activations : MemoryBound

def TrainingMemory.totalMax (tm : TrainingMemory) : ℕ :=
  tm.parameters.maxBytes + tm.gradients.maxBytes +
  tm.optimizerState.maxBytes + tm.activations.maxBytes

def TrainingMemory.totalMin (tm : TrainingMemory) : ℕ :=
  tm.parameters.minBytes + tm.gradients.minBytes +
  tm.optimizerState.minBytes + tm.activations.minBytes

-- If max estimate fits, any actual usage fits.
theorem training_fits_if_max_fits (tm : TrainingMemory) (device : DeviceMemory) (actual : ℕ) :
  tm.totalMax ≤ device.availableBytes → tm.totalMin ≤ actual → actual ≤ tm.totalMax → actual ≤ device.availableBytes := by
  intro h_max h_min h_actual
  omega

end TensorMemory
