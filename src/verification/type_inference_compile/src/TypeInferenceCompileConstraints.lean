import TypeInferenceCompile

/-!
# TypeInferenceCompileConstraints — hand-written constraints and proofs for `TypeInferenceCompile`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `TypeInferenceCompile` live here; the generated model lives in
`TypeInferenceCompile.lean` and may be replaced wholesale by regeneration.
-/

namespace TypeInferenceCompile

theorem infer_add_rejects_bool_operand (n : Nat) (b : Bool) :
  infer (Expr.add (Expr.litNat n) (Expr.litBool b)) = none := by
  simp [infer]


end TypeInferenceCompile
