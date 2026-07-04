import NogcCompile

/-!
# NogcCompileConstraints — hand-written constraints and proofs for `NogcCompile`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `NogcCompile` live here; the generated model lives in
`NogcCompile.lean` and may be replaced wholesale by regeneration.
-/

namespace NogcCompile

theorem gc_alloc_singleton_not_nogc :
  ¬ nogc [Instr.gcAlloc] := by
  intro h
  exact h Instr.gcAlloc (by simp) rfl


end NogcCompile
