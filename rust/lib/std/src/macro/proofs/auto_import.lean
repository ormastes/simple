namespace MacroAutoImport

/-!
# Macro Auto-Import Model

This model formalizes the macro import/export and `auto import` semantics from
`doc/depedency_tracking.md` (v5).

## Key Properties

1. Macros are NOT included in glob imports by default
2. Only macros listed in `auto import` participate in glob imports
3. Explicit macro imports always work regardless of `auto import`
4. Macros listed in `auto import` are included in:
   - `use module.*`
   - `common use module.*`
   - `export use module.*`

## Invariants

1. **Glob doesn't leak**: If macro `m` is not in `auto import`, then `m` is never
   in the result of `globImport`
2. **Explicit always works**: Explicit `use module.macroName` always imports the macro
   if it exists and is public
3. **Two-phase visibility**: Macro export happens in Phase 1 (module exports it),
   glob participation happens in Phase 2 (directory's `autoImports` lists it)
-/

/-- Symbol kind distinguishes macros from other symbols. -/
inductive SymKind
  | valueOrType  -- Functions, types, constants
  | macro        -- Macro definitions
deriving DecidableEq, Repr

/-- A fully-qualified symbol. -/
structure Symbol where
  modulePath : String
  name : String
  kind : SymKind
deriving DecidableEq, Repr

/-- Auto-import declaration from __init__.spl. -/
structure AutoImport where
  fromModule : String
  macroName : String
deriving DecidableEq, Repr

/-- What a module publicly exports. -/
structure ModuleExports where
  nonMacros : List Symbol  -- Public non-macro symbols
  macros : List Symbol     -- Public macros
deriving Repr

/-- Directory manifest for macro handling. -/
structure DirManifest where
  name : String
  autoImports : List AutoImport  -- auto import declarations
deriving Repr

/-- Check if a macro is in the auto-import list. -/
def isAutoImported (m : DirManifest) (sym : Symbol) : Bool :=
  sym.kind == SymKind.macro &&
  m.autoImports.any (fun ai => ai.fromModule == sym.modulePath && ai.macroName == sym.name)

/-- Filter macros that are in auto-import list. -/
def autoImportedMacros (m : DirManifest) (exports : ModuleExports) : List Symbol :=
  exports.macros.filter (isAutoImported m)

/-- Glob import result: non-macros + auto-imported macros only. -/
def globImport (m : DirManifest) (exports : ModuleExports) : List Symbol :=
  exports.nonMacros ++ autoImportedMacros m exports

/-- Explicit import: always works for any public symbol. -/
def explicitImport (exports : ModuleExports) (name : String) : Option Symbol :=
  (exports.nonMacros ++ exports.macros).find? (·.name == name)

/-- Well-formedness: nonMacros contains only non-macros. -/
def wellFormedExports (exports : ModuleExports) : Prop :=
  (∀ s ∈ exports.nonMacros, s.kind = SymKind.valueOrType) ∧
  (∀ s ∈ exports.macros, s.kind = SymKind.macro)

/-- Key theorem: Macros not in auto-import are never in glob import result
    (assuming well-formed exports). -/
theorem glob_doesnt_leak_macros_wf (m : DirManifest) (exports : ModuleExports)
    (hwf : wellFormedExports exports) (sym : Symbol) :
    sym.kind = SymKind.macro →
    isAutoImported m sym = false →
    sym ∉ globImport m exports := by
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

/-- All non-macros are always in glob import. -/
theorem nonmacros_always_globbed (m : DirManifest) (exports : ModuleExports) (sym : Symbol) :
    sym ∈ exports.nonMacros →
    sym ∈ globImport m exports := by
  intro hmem
  unfold globImport
  rw [List.mem_append]
  left
  exact hmem

/-- Auto-imported macros are in glob import. -/
theorem auto_imported_in_glob (m : DirManifest) (exports : ModuleExports) (sym : Symbol) :
    sym ∈ exports.macros →
    isAutoImported m sym = true →
    sym ∈ globImport m exports := by
  intro hmacro hauto
  unfold globImport
  rw [List.mem_append]
  right
  unfold autoImportedMacros
  rw [List.mem_filter]
  exact ⟨hmacro, hauto⟩

/-- Glob import preserves well-formedness: result symbols come from exports. -/
theorem glob_subset (m : DirManifest) (exports : ModuleExports) (sym : Symbol) :
    sym ∈ globImport m exports →
    sym ∈ exports.nonMacros ∨ sym ∈ exports.macros := by
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

/-- Empty auto-import means autoImportedMacros is empty. -/
theorem empty_auto_import_no_macros (exports : ModuleExports) :
    let m : DirManifest := ⟨"", []⟩
    autoImportedMacros m exports = [] := by
  simp [autoImportedMacros, isAutoImported, List.filter_eq_nil_iff]

/-- Composition: glob import of combined exports. -/
def combineExports (e1 e2 : ModuleExports) : ModuleExports :=
  { nonMacros := e1.nonMacros ++ e2.nonMacros
    macros := e1.macros ++ e2.macros }

/-- AutoImported macros from combined exports is the combination. -/
theorem autoImported_combine (m : DirManifest) (e1 e2 : ModuleExports) :
    autoImportedMacros m (combineExports e1 e2) =
    autoImportedMacros m e1 ++ autoImportedMacros m e2 := by
  unfold autoImportedMacros combineExports
  simp [List.filter_append]

end MacroAutoImport
