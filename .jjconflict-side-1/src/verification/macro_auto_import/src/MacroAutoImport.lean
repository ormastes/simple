namespace MacroAutoImport
/-
  # Macro Auto-Import Model
  
  Key Properties:
  1. Macros are NOT included in glob imports by default
  2. Only macros listed in `auto import` participate in glob imports
-/
inductive SymKind
  | valueOrType
  | macro
deriving DecidableEq, Repr, BEq

structure Symbol where
  modulePath : String
  name : String
  kind : SymKind
deriving DecidableEq, Repr

structure AutoImport where
  fromModule : String
  macroName : String
deriving DecidableEq, Repr

structure ModuleExports where
  nonMacros : List Symbol
  macros : List Symbol
deriving Repr

structure DirManifest where
  name : String
  autoImports : List AutoImport
deriving Repr

def isAutoImported (m : DirManifest) (sym : Symbol) : Bool :=
  sym.kind == SymKind.macro &&
  m.autoImports.any (fun ai => ai.fromModule == sym.modulePath && ai.macroName == sym.name)

def autoImportedMacros (m : DirManifest) (exports : ModuleExports) : List Symbol :=
  exports.macros.filter (isAutoImported m)

def globImport (m : DirManifest) (exports : ModuleExports) : List Symbol :=
  exports.nonMacros ++ autoImportedMacros m exports

def wellFormedExports (exports : ModuleExports) : Prop :=
  (∀ s ∈ exports.nonMacros, s.kind = SymKind.valueOrType) ∧
  (∀ s ∈ exports.macros, s.kind = SymKind.macro)

theorem glob_doesnt_leak_macros_wf (m : DirManifest) (exports : ModuleExports) (hwf : wellFormedExports exports) (sym : Symbol) :
  sym.kind = SymKind.macro → isAutoImported m sym = false → sym ∉ globImport m exports := by
  intro hkind hnotauto hmem
  unfold globImport at hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl hnonmacro =>
    have h := hwf.1 sym hnonmacro
    rw [h] at hkind
    contradiction
  | inr hauto =>
    unfold autoImportedMacros at hauto
    rw [List.mem_filter] at hauto
    obtain ⟨_, hfilter⟩ := hauto
    simp [hfilter] at hnotauto

theorem nonmacros_always_globbed (m : DirManifest) (exports : ModuleExports) (sym : Symbol) :
  sym ∈ exports.nonMacros → sym ∈ globImport m exports := by
  intro hmem
  unfold globImport
  rw [List.mem_append]
  left
  exact hmem

theorem auto_imported_in_glob (m : DirManifest) (exports : ModuleExports) (sym : Symbol) :
  sym ∈ exports.macros → isAutoImported m sym = true → sym ∈ globImport m exports := by
  intro hmacro hauto
  unfold globImport
  rw [List.mem_append]
  right
  unfold autoImportedMacros
  rw [List.mem_filter]
  exact ⟨hmacro, hauto⟩

theorem glob_subset (m : DirManifest) (exports : ModuleExports) (sym : Symbol) :
  sym ∈ globImport m exports → sym ∈ exports.nonMacros ∨ sym ∈ exports.macros := by
  intro hmem
  unfold globImport at hmem
  rw [List.mem_append] at hmem
  cases hmem with
  | inl h => left; exact h
  | inr h =>
    right
    unfold autoImportedMacros at h
    rw [List.mem_filter] at h
    exact h.1

theorem empty_auto_import_no_macros (exports : ModuleExports) :
  autoImportedMacros { name := "", autoImports := [] } exports = [] := by
  simp [autoImportedMacros, isAutoImported, List.filter_eq_nil_iff]

end MacroAutoImport
