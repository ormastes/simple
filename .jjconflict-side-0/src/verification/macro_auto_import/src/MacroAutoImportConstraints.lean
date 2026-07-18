import MacroAutoImport

/-!
# MacroAutoImportConstraints — hand-written constraints and proofs for `MacroAutoImport`

MANUAL-OWNED: `simple gen-lean` never writes this file. All hand-written
theorems for `MacroAutoImport` live here; the generated model lives in
`MacroAutoImport.lean` and may be replaced wholesale by regeneration.
-/

namespace MacroAutoImport

theorem auto_import_true_implies_macro (m : DirManifest) (sym : Symbol) :
  isAutoImported m sym = true → sym.kind = SymKind.macro := by
  intro h
  unfold isAutoImported at h
  rw [Bool.and_eq_true] at h
  cases hkind : sym.kind
  · have hf : (SymKind.valueOrType == SymKind.macro) = false := rfl
    rw [hkind, hf] at h
    cases h.1
  · rfl

theorem empty_auto_import_glob_nonmacros (exports : ModuleExports) :
  globImport { name := "", autoImports := [] } exports = exports.nonMacros := by
  simp [globImport, autoImportedMacros, isAutoImported, List.filter_eq_nil_iff]


end MacroAutoImport
