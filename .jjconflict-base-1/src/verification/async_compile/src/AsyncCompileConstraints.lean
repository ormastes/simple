import AsyncCompile

/-!
# AsyncCompileConstraints — hand-written constraints and proofs for `AsyncCompile`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `AsyncCompile` live here; the generated model lives in
`AsyncCompile.lean` and may be replaced wholesale by regeneration.
-/

namespace AsyncCompile

theorem wait_pipeline_not_safe :
  ¬ pipelineSafe [Effect.wait] := by
  intro h
  have hw : is_async Effect.wait = true := h _ (by simp)
  simp [is_async] at hw


end AsyncCompile
