/-
  DynTrait.lean - Formal verification of dynamic trait object type inference

  This module formalizes:
  - Coercion from concrete types to dyn Trait
  - Method dispatch on dyn Trait objects
  - Unification rules for dynTrait types
  - Soundness of dyn trait coercion
-/

import Classes
import Traits

-- Using types from Classes: Ty, TyVar, FieldDef, MethodDef
-- Using types from Traits: TraitEnv, TraitDef, TraitMethod, ImplRegistry, implementsTrait, lookupTrait, lookupTraitMethod

--==============================================================================
-- Dyn Trait Coercion
--==============================================================================

/-- Check if a concrete type can be coerced to dyn Trait.
    A concrete type can be coerced if it implements the trait. -/
def canCoerceToDyn (registry : ImplRegistry) (concreteTy : Ty) (traitName : String) : Bool :=
  implementsTrait registry concreteTy traitName

/-- Perform the coercion: returns the dyn Trait type if coercion is valid -/
def coerceToDyn (registry : ImplRegistry) (concreteTy : Ty) (traitName : String) : Option Ty :=
  if canCoerceToDyn registry concreteTy traitName then
    some (Ty.dynTrait traitName)
  else
    none

--==============================================================================
-- Dyn Trait Method Resolution
--==============================================================================

/-- Resolve a method call on a dyn Trait object.
    Looks up the method in the trait definition. -/
def inferDynMethodCall (env : TraitEnv) (traitName methodName : String) (argTys : List Ty) : Option Ty :=
  match lookupTrait env traitName with
  | some trait =>
      match lookupTraitMethod trait methodName with
      | some method =>
          if method.params == argTys then
            some method.ret
          else
            none
      | none => none
  | none => none

--==============================================================================
-- Dyn Trait Unification Rules
--==============================================================================

/-- Two dyn Trait types unify only if they refer to the same trait -/
def unifyDynTrait (t1 t2 : Ty) : Bool :=
  match t1, t2 with
  | Ty.dynTrait n1, Ty.dynTrait n2 => n1 == n2
  | _, _ => false

--==============================================================================
-- Theorems
--==============================================================================

/-- Coercion soundness: if coercion succeeds, all trait methods are available
    on the dyn type (via inferDynMethodCall). -/
theorem dynCoercion_sound (env : TraitEnv) (registry : ImplRegistry)
    (concreteTy : Ty) (traitName : String) (trait : TraitDef)
    (method : TraitMethod) (argTys : List Ty) (retTy : Ty)
    (h_nodup : (trait.methods.map TraitMethod.name).Nodup)
    (h_coerce : canCoerceToDyn registry concreteTy traitName = true)
    (h_trait : lookupTrait env traitName = some trait)
    (h_method : method ∈ trait.methods)
    (h_params : method.params = argTys)
    (h_ret : method.ret = retTy) :
    inferDynMethodCall env traitName method.name argTys = some retTy := by
  unfold inferDynMethodCall
  simp only [h_trait]
  -- With unique method names, lookupTraitMethod finds exactly this method
  have h_found : lookupTraitMethod trait method.name = some method := by
    unfold lookupTraitMethod
    exact find_unique_by_name trait.methods TraitMethod.name method h_method h_nodup
  simp only [h_found, h_params, beq_self_eq_true, ↓reduceIte, h_ret]

/-- Dyn dispatch is deterministic: method resolution returns at most one type -/
theorem dynDispatch_deterministic (env : TraitEnv)
    (traitName methodName : String) (argTys : List Ty) (retTy1 retTy2 : Ty) :
    inferDynMethodCall env traitName methodName argTys = some retTy1 →
    inferDynMethodCall env traitName methodName argTys = some retTy2 →
    retTy1 = retTy2 := by
  intro h1 h2
  rw [h1] at h2
  cases h2
  rfl

/-- Dyn dispatch matches static dispatch: calling a method through dyn Trait
    returns the same type as calling through static dispatch (trait method call). -/
theorem dynDispatch_matches_static (env : TraitEnv) (registry : ImplRegistry)
    (traitName methodName : String) (selfTy : Ty) (argTys : List Ty) (retTy : Ty) :
    implementsTrait registry selfTy traitName = true →
    inferTraitMethodCall env registry traitName methodName selfTy argTys = some retTy →
    inferDynMethodCall env traitName methodName argTys = some retTy := by
  intro h_impl h_static
  unfold inferTraitMethodCall at h_static
  unfold inferDynMethodCall
  -- Both look up the same trait and method
  cases h_trait : lookupTrait env traitName with
  | none => simp [h_trait] at h_static
  | some trait =>
    simp only [h_trait] at h_static ⊢
    cases h_method : lookupTraitMethod trait methodName with
    | none => simp [h_method] at h_static
    | some method =>
      simp only [h_method] at h_static ⊢
      -- Static dispatch checks implementsTrait AND params match
      -- If static succeeds, params match, so dyn also succeeds
      simp only [h_impl, Bool.true_and] at h_static
      -- h_static now is: if method.params == argTys then some method.ret else none = some retTy
      exact h_static

/-- Dyn Trait unification rules: dyn Trait only unifies with itself or type vars.
    Two dynTrait types unify iff they refer to the same trait name. -/
theorem dynTrait_unification_rules (n1 n2 : String) :
    unifyDynTrait (Ty.dynTrait n1) (Ty.dynTrait n2) = (n1 == n2) := by
  unfold unifyDynTrait
  rfl

/-- Dyn Trait does not unify with non-dynTrait types (excluding type variables) -/
theorem dynTrait_no_unify_concrete (traitName : String) :
    unifyDynTrait (Ty.dynTrait traitName) Ty.int = false := by
  unfold unifyDynTrait
  rfl

/-- Coercion produces the correct dyn type -/
theorem coerce_produces_dynTrait (registry : ImplRegistry) (concreteTy : Ty) (traitName : String) :
    canCoerceToDyn registry concreteTy traitName = true →
    coerceToDyn registry concreteTy traitName = some (Ty.dynTrait traitName) := by
  intro h
  unfold coerceToDyn
  simp [h]

/-- Coercion fails when trait is not implemented -/
theorem coerce_fails_without_impl (registry : ImplRegistry) (concreteTy : Ty) (traitName : String) :
    canCoerceToDyn registry concreteTy traitName = false →
    coerceToDyn registry concreteTy traitName = none := by
  intro h
  unfold coerceToDyn
  simp [h]
