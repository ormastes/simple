import VisibilityExport

/-!
# VisibilityExportConstraints — hand-written constraints and proofs for `VisibilityExport`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `VisibilityExport` live here; the generated model lives in
`VisibilityExport.lean` and may be replaced wholesale by regeneration.
-/

namespace VisibilityExport

theorem private_symbol_under_public_path_private (path : List Visibility)
    (hpath : ancestorVisibility path = Visibility.pub) :
    visibilityMeet Visibility.priv (ancestorVisibility path) = Visibility.priv := by
  rw [hpath]
  rfl


end VisibilityExport
