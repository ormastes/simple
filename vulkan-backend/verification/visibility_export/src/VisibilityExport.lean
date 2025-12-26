namespace VisibilityExport

/-!
# Visibility and Export Model

This model formalizes the visibility and export rules from `doc/depedency_tracking.md` (v5).

## Key Properties

1. Visibility is the **intersection** of declaration visibility and ancestor visibility
2. A directory's public API consists only of:
   - Child modules declared as `pub mod` in its `__init__.spl`
   - Symbols listed in `export use` inside that same `__init__.spl`
3. Nothing inside a child `.spl` file can make itself "more public" than its
   directory's `__init__.spl` allows
-/

/-- Visibility of a declaration or module. Using pub/priv to avoid Lean reserved words. -/
inductive Visibility
  | pub   -- public
  | priv  -- private
deriving DecidableEq, Repr, BEq

/-- A symbol identifier. -/
structure SymbolId where
  name : String
deriving DecidableEq, Repr

/-- A module can contain symbols with visibility. -/
structure Symbol where
  id : SymbolId
  visibility : Visibility
deriving Repr

/-- A module declaration in __init__.spl. -/
structure ModDecl where
  name : String
  isPub : Bool  -- pub mod vs mod
deriving Repr

/-- A directory manifest (__init__.spl). -/
structure DirManifest where
  name : String
  children : List ModDecl
  exports : List SymbolId  -- export use declarations
deriving Repr

/-- Check if a child module is declared public in the manifest. -/
def DirManifest.isChildPublic (m : DirManifest) (childName : String) : Bool :=
  m.children.any (fun d => d.name == childName && d.isPub)

/-- Check if a symbol is explicitly exported. -/
def DirManifest.isExported (m : DirManifest) (sym : SymbolId) : Bool :=
  m.exports.any (· == sym)

/-- Module contents: symbols defined in a module file. -/
structure ModuleContents where
  symbols : List Symbol
deriving Repr

/-- Get visibility of a symbol from module contents. -/
def ModuleContents.symbolVisibility (mc : ModuleContents) (sym : SymbolId) : Option Visibility :=
  mc.symbols.find? (·.id == sym) |>.map (·.visibility)

/-- Effective visibility combines declaration visibility with directory control.
    A symbol is externally visible only if:
    1. It is declared `pub` in its module
    2. Its module is declared `pub mod` in the directory's __init__.spl
    3. Either it's in the export list, or its module is public
-/
def effectiveVisibility (manifest : DirManifest) (moduleName : String)
    (mc : ModuleContents) (sym : SymbolId) : Visibility :=
  match mc.symbolVisibility sym with
  | none => Visibility.priv  -- Symbol not found
  | some Visibility.priv => Visibility.priv  -- Declaration is private
  | some Visibility.pub =>
      -- Symbol is declared public; check if directory allows export
      if manifest.isChildPublic moduleName then
        if manifest.isExported sym then Visibility.pub
        else Visibility.priv  -- Not in export list
      else Visibility.priv  -- Module not public

/-- Alternative: if we include glob exports (export use module.*), check module public. -/
def effectiveVisibilityWithGlob (manifest : DirManifest) (moduleName : String)
    (mc : ModuleContents) (sym : SymbolId) (hasGlobExport : Bool) : Visibility :=
  match mc.symbolVisibility sym with
  | none => Visibility.priv
  | some Visibility.priv => Visibility.priv
  | some Visibility.pub =>
      if manifest.isChildPublic moduleName then
        if manifest.isExported sym || hasGlobExport then Visibility.pub
        else Visibility.priv
      else Visibility.priv

/-- A private symbol cannot become public regardless of directory settings. -/
theorem private_stays_private (manifest : DirManifest) (moduleName : String)
    (mc : ModuleContents) (sym : SymbolId) :
    mc.symbolVisibility sym = some Visibility.priv →
    effectiveVisibility manifest moduleName mc sym = Visibility.priv := by
  intro h
  unfold effectiveVisibility
  simp [h]

/-- A symbol in a private module cannot become public. -/
theorem private_module_restricts (manifest : DirManifest) (moduleName : String)
    (mc : ModuleContents) (sym : SymbolId) :
    manifest.isChildPublic moduleName = false →
    effectiveVisibility manifest moduleName mc sym = Visibility.priv := by
  intro hpriv
  unfold effectiveVisibility
  cases h : mc.symbolVisibility sym with
  | none => rfl
  | some vis =>
    cases vis with
    | priv => rfl
    | pub => simp [hpriv]

/-- A symbol must be explicitly exported to be visible externally. -/
theorem must_be_exported (manifest : DirManifest) (moduleName : String)
    (mc : ModuleContents) (sym : SymbolId) :
    effectiveVisibility manifest moduleName mc sym = Visibility.pub →
    manifest.isExported sym = true := by
  intro h
  unfold effectiveVisibility at h
  cases hopt : mc.symbolVisibility sym with
  | none => simp [hopt] at h
  | some vis =>
    simp [hopt] at h
    cases vis with
    | priv => simp at h
    | pub =>
      simp at h
      split at h
      · split at h
        · assumption
        · contradiction
      · contradiction

/-- Visibility is monotonically restricted: intersection of visibilities. -/
def visibilityMeet (v1 v2 : Visibility) : Visibility :=
  match v1, v2 with
  | Visibility.pub, Visibility.pub => Visibility.pub
  | _, _ => Visibility.priv

/-- Meet is commutative. -/
theorem meet_comm (v1 v2 : Visibility) :
    visibilityMeet v1 v2 = visibilityMeet v2 v1 := by
  cases v1 <;> cases v2 <;> rfl

/-- Meet is associative. -/
theorem meet_assoc (v1 v2 v3 : Visibility) :
    visibilityMeet (visibilityMeet v1 v2) v3 = visibilityMeet v1 (visibilityMeet v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;> rfl

/-- Private is absorbing element for meet. -/
theorem meet_private_left (v : Visibility) :
    visibilityMeet Visibility.priv v = Visibility.priv := by
  cases v <;> rfl

theorem meet_private_right (v : Visibility) :
    visibilityMeet v Visibility.priv = Visibility.priv := by
  cases v <;> rfl

/-- Public is identity element for meet. -/
theorem meet_public_left (v : Visibility) :
    visibilityMeet Visibility.pub v = v := by
  cases v <;> rfl

theorem meet_public_right (v : Visibility) :
    visibilityMeet v Visibility.pub = v := by
  cases v <;> rfl

/-- Ancestor visibility model: effective visibility through a path. -/
def ancestorVisibility (path : List Visibility) : Visibility :=
  path.foldl visibilityMeet Visibility.pub

/-- Helper: foldl with priv absorbs. -/
theorem foldl_priv_absorbs (vs : List Visibility) :
    List.foldl visibilityMeet Visibility.priv vs = Visibility.priv := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [List.foldl, meet_private_left, ih]

/-- If any ancestor is private, result is private. -/
theorem any_private_means_private (path : List Visibility) :
    Visibility.priv ∈ path →
    ancestorVisibility path = Visibility.priv := by
  intro h
  induction path with
  | nil => simp at h
  | cons v vs ih =>
    unfold ancestorVisibility List.foldl
    cases hv : v with
    | priv =>
      simp [visibilityMeet, foldl_priv_absorbs]
    | pub =>
      simp [visibilityMeet]
      cases h with
      | head => simp_all
      | tail _ hmem =>
        unfold ancestorVisibility at ih
        exact ih hmem

/-- All public ancestors means public result. -/
theorem all_public_means_public (path : List Visibility) :
    (∀ v ∈ path, v = Visibility.pub) →
    ancestorVisibility path = Visibility.pub := by
  intro h
  induction path with
  | nil => rfl
  | cons v vs ih =>
    unfold ancestorVisibility List.foldl
    have hv : v = Visibility.pub := h v (List.mem_cons_self ..)
    rw [hv]
    simp [visibilityMeet]
    unfold ancestorVisibility at ih
    apply ih
    intro v' hv'
    exact h v' (List.mem_cons_of_mem v hv')

end VisibilityExport
