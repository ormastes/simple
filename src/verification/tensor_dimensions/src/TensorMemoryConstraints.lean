import TensorMemory

/-!
# TensorMemoryConstraints — hand-written constraints and proofs for `TensorMemory`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `TensorMemory` live here; the generated model lives in
`TensorMemory.lean` and may be replaced wholesale by regeneration.
-/

namespace TensorMemory

theorem training_total_min_le_max (tm : TrainingMemory)
    (hp : tm.parameterBytes.minBytes ≤ tm.parameterBytes.maxBytes)
    (hg : tm.gradients.minBytes ≤ tm.gradients.maxBytes)
    (ho : tm.optimizerState.minBytes ≤ tm.optimizerState.maxBytes)
    (ha : tm.activations.minBytes ≤ tm.activations.maxBytes) :
    tm.totalMin ≤ tm.totalMax := by
  unfold TrainingMemory.totalMin TrainingMemory.totalMax
  omega


end TensorMemory
