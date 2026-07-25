import Generics

/-!
# GenericsConstraints — hand-written constraints and proofs for `Generics`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `Generics` live here; the generated model lives in
`Generics.lean` and may be replaced wholesale by regeneration.
-/

namespace Generics

theorem apply_single_subst_var (v : TyVar) (t : Ty) :
  applySubst (singleSubst v t) (Ty.var v) = t := by
  simp [applySubst, singleSubst, substLookup]


end Generics
