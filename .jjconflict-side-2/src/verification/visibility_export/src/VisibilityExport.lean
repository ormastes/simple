namespace VisibilityExport
/-
  # Visibility and Export Model
  
  This model formalizes the visibility and export rules.
  
  ## Key Properties
  1. Visibility is the intersection of declaration visibility and ancestor visibility
  2. A directory's public API consists only of child modules declared as `pub mod`
-/
inductive Visibility
  | pub
  | priv
deriving DecidableEq, Repr, BEq

structure SymbolId where
  name : String
deriving DecidableEq, Repr, BEq

structure Symbol where
  id : SymbolId
  visibility : Visibility
deriving DecidableEq, Repr

structure ModDecl where
  name : String
  isPub : Bool
deriving DecidableEq, Repr

structure DirManifest where
  name : String
  children : List ModDecl
  exports : List SymbolId
deriving Repr

structure ModuleContents where
  symbols : List Symbol
deriving Repr

def DirManifest.isChildPublic (m : DirManifest) (childName : String) : Bool :=
  m.children.any (fun d => d.name == childName && d.isPub)

def DirManifest.isExported (m : DirManifest) (sym : SymbolId) : Bool :=
  m.exports.any (fun exported => exported == sym)

def ModuleContents.symbolVisibility (mc : ModuleContents) (sym : SymbolId) : Option Visibility :=
  (mc.symbols.find? (fun s => s.id == sym)).map (fun s => s.visibility)

def visibilityMeet (v1 : Visibility) (v2 : Visibility) : Visibility :=
  match v1, v2 with
  | Visibility.pub, Visibility.pub => Visibility.pub
  | _, _ => Visibility.priv

def ancestorVisibility (path : List Visibility) : Visibility :=
  path.foldl visibilityMeet Visibility.pub

theorem meet_comm (v1 : Visibility) (v2 : Visibility) :
  visibilityMeet v1 v2 = visibilityMeet v2 v1 := by
  cases v1 <;> cases v2 <;> rfl

theorem meet_assoc (v1 : Visibility) (v2 : Visibility) (v3 : Visibility) :
  visibilityMeet (visibilityMeet v1 v2) v3 = visibilityMeet v1 (visibilityMeet v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;> rfl

theorem meet_private_left (v : Visibility) :
  visibilityMeet Visibility.priv v = Visibility.priv := by
  cases v <;> rfl

theorem meet_private_right (v : Visibility) :
  visibilityMeet v Visibility.priv = Visibility.priv := by
  cases v <;> rfl

theorem meet_public_left (v : Visibility) :
  visibilityMeet Visibility.pub v = v := by
  cases v <;> rfl

theorem meet_public_right (v : Visibility) :
  visibilityMeet v Visibility.pub = v := by
  cases v <;> rfl

theorem foldl_priv_absorbs (vs : List Visibility) :
  List.foldl visibilityMeet Visibility.priv vs = Visibility.priv := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [List.foldl, meet_private_left, ih]

theorem any_private_means_private (path : List Visibility) :
  Visibility.priv ∈ path → ancestorVisibility path = Visibility.priv := by
  intro h
  induction path with
  | nil => simp at h
  | cons v vs ih =>
    unfold ancestorVisibility List.foldl
    cases hv : v with
    | priv => simp [visibilityMeet, foldl_priv_absorbs]
    | pub =>
      simp [visibilityMeet]
      cases h with
      | head => simp_all
      | tail _ hmem => unfold ancestorVisibility at ih; exact ih hmem

theorem all_public_means_public (path : List Visibility) :
  (∀ v ∈ path, v = Visibility.pub) → ancestorVisibility path = Visibility.pub := by
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
