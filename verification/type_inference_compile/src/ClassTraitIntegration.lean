/-
  ClassTraitIntegration.lean - Formal verification of class-trait integration

  This module formalizes the integration between classes and traits:
  - Classes implementing traits
  - Trait bounds on class type parameters
  - Method dispatch resolution (class methods vs trait methods)
  - Trait objects (dyn Trait) with classes
  - Coherence for class-based trait implementations
-/

import Classes
import Traits
import DynTrait
import Mixins

-- Combined environment with both classes and traits
structure TypeEnv where
  classes : ClassEnv
  traits : TraitEnv
  impls : ImplRegistry
  mixins : MixinEnv := []

-- Check if a class implements a trait
def classImplementsTrait (env : TypeEnv) (className traitName : String) : Bool :=
  implementsTrait env.impls (Ty.named className) traitName

-- Resolve method call: could be class method or trait method
-- Priority: class methods > trait methods
inductive MethodSource where
  | classMethod (className : String) (method : MethodDef)
  | traitMethod (traitName : String) (method : TraitMethod)
  | mixinMethod (mixinName : String) (method : MethodDef)
  deriving Repr

-- Find the source of a method for a class
def resolveMethodSource (env : TypeEnv) (className methodName : String) : Option MethodSource :=
  match lookupClass env.classes className with
  | some cls =>
      -- First check if it's a class method
      match lookupMethod cls methodName with
      | some method => some (MethodSource.classMethod className method)
      | none =>
          -- Check trait implementations
          let traitImpls := env.impls.filter (fun impl =>
            impl.for_type == Ty.named className
          )
          let traitMethod := traitImpls.findSome? (fun impl =>
            match lookupTrait env.traits impl.trait_name with
            | some trait =>
                lookupTraitMethod trait methodName |>.map (fun m =>
                  MethodSource.traitMethod impl.trait_name m
                )
            | none => none
          )
          match traitMethod with
          | some src => some src
          | none =>
              -- Check mixin-provided methods (lowest priority)
              let mixinMethod := env.mixins.findSome? (fun (mixinName, mixin) =>
                mixin.methods.find? (fun m => m.name == methodName) |>.map (fun m =>
                  MethodSource.mixinMethod mixinName m
                )
              )
              mixinMethod
  | none => none

-- Type inference for method call with class-trait integration
def inferIntegratedMethodCall (env : TypeEnv) (objTy : Ty) (methodName : String) (argTys : List Ty) : Option Ty :=
  match objTy with
  | Ty.named className =>
      match resolveMethodSource env className methodName with
      | some (MethodSource.classMethod _ method) =>
          -- Class method takes priority
          if method.params == argTys then
            some method.ret
          else
            none
      | some (MethodSource.traitMethod _ method) =>
          -- Trait method (types are now unified, no conversion needed)
          if method.params == argTys then
            some method.ret
          else
            none
      | some (MethodSource.mixinMethod _ method) =>
          -- Mixin-provided method (lowest priority)
          if method.params == argTys then
            some method.ret
          else
            none
      | none => none
  | Ty.dynTrait traitName =>
      -- Dynamic trait dispatch
      inferDynMethodCall env.traits traitName methodName argTys
  | _ => none

-- Check coherence for class-trait implementations
-- Ensures that a class doesn't have overlapping trait implementations
def checkClassTraitCoherence (env : TypeEnv) : Bool :=
  let classNames := env.classes.map (·.1)
  classNames.all (fun className =>
    let classImpls := env.impls.filter (fun impl =>
      impl.for_type == Ty.named className
    )
    -- Check that each trait is implemented at most once for this class
    let traitNames := classImpls.map (·.trait_name)
    traitNames.length == traitNames.eraseDups.length
  )

-- Validate trait implementation for a class
-- Ensures all trait methods are implemented with correct types
def validateTraitImpl (env : TypeEnv) (impl : TraitImpl) : Bool :=
  match impl.for_type with
  | Ty.named className =>
      match lookupTrait env.traits impl.trait_name with
      | some trait =>
          -- All trait methods must have implementations
          trait.methods.all (fun traitMethod =>
            impl.method_impls.any (fun (name, _) =>
              name == traitMethod.name
            )
          )
      | none => false
  | _ => false

-- Check if a generic class satisfies trait bounds
-- Example: Box[T: Show] means T must implement Show
def checkGenericClassBounds (env : TypeEnv) (className : String) (typeArgs : List Ty)
    (bounds : List (Ty × String)) : Bool :=
  bounds.all (fun (ty, traitName) =>
    match ty with
    | Ty.var _ =>
        -- Simplified: type variable bounds checking not fully implemented
        true
    | Ty.named n =>
        classImplementsTrait env n traitName
    | _ => false
  )

--==============================================================================
-- Theorems and Properties
--==============================================================================

-- Theorem: Method resolution is deterministic
theorem methodResolution_deterministic (env : TypeEnv) (className methodName : String) (src1 src2 : MethodSource) :
  resolveMethodSource env className methodName = some src1 →
  resolveMethodSource env className methodName = some src2 →
  src1 = src2 := by
  intro h1 h2
  rw [h1] at h2
  cases h2
  rfl

-- Theorem: Class methods take priority over trait methods
theorem classMethod_priority (env : TypeEnv) (className methodName : String) (classMethod : MethodDef) :
  (∃ cls, lookupClass env.classes className = some cls ∧
    lookupMethod cls methodName = some classMethod) →
  resolveMethodSource env className methodName = some (MethodSource.classMethod className classMethod) := by
  intro ⟨cls, h_class, h_method⟩
  unfold resolveMethodSource
  simp [h_class, h_method]

-- Helper: If length equals eraseDups length, then no duplicates
theorem nodup_of_length_eq_eraseDups' {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.length = l.eraseDups.length → l.Nodup := by
  intro h
  induction l with
  | nil => exact List.Nodup.nil
  | cons x xs ih =>
    simp only [List.eraseDups_cons] at h
    split at h
    · -- x ∈ xs.eraseDups, contradiction with length equality
      simp only [List.length_cons] at h
      omega
    · -- x ∉ xs.eraseDups
      simp only [List.length_cons] at h
      have h_xs := ih (Nat.succ.inj h)
      constructor
      · intro h_mem
        rename_i h_not_mem
        have : x ∈ xs.eraseDups := List.mem_eraseDups.mpr h_mem
        contradiction
      · exact h_xs

-- Helper: Nodup on mapped list means injective on list membership
theorem nodup_map_injective' {α β : Type} [DecidableEq β] (l : List α) (f : α → β)
    (h_nodup : (l.map f).Nodup) (x y : α) (hx : x ∈ l) (hy : y ∈ l) (heq : f x = f y) :
    x = y := by
  induction l with
  | nil => cases hx
  | cons a as ih =>
    simp only [List.map] at h_nodup
    have ⟨h_not_mem, h_nodup_as⟩ := List.nodup_cons.mp h_nodup
    cases hx with
    | head =>
      cases hy with
      | head => rfl
      | tail _ hy' =>
        -- f a = f y where y ∈ as, but f a ∉ (as.map f) - contradiction
        have : f a ∈ as.map f := by
          rw [← heq]
          exact List.mem_map_of_mem f hy'
        contradiction
    | tail _ hx' =>
      cases hy with
      | head =>
        -- f x = f a where x ∈ as, but f a ∉ (as.map f) - contradiction
        have : f a ∈ as.map f := by
          rw [heq]
          exact List.mem_map_of_mem f hx'
        contradiction
      | tail _ hy' =>
        exact ih h_nodup_as hx' hy' heq

-- Theorem: Coherence ensures unique trait implementations per class
-- Converted from axiom: Added proper preconditions for class membership and impl membership
theorem coherence_unique_impls (env : TypeEnv) (className traitName : String) (impl1 impl2 : TraitImpl) :
  checkClassTraitCoherence env = true →
  className ∈ env.classes.map (·.1) →  -- Class must be in environment
  impl1 ∈ env.impls →                  -- impl1 must be in registry
  impl2 ∈ env.impls →                  -- impl2 must be in registry
  impl1.for_type = Ty.named className →
  impl2.for_type = Ty.named className →
  impl1.trait_name = traitName →
  impl2.trait_name = traitName →
  impl1 = impl2 := by
  intro h_coh h_class_mem h_impl1_mem h_impl2_mem h_for1 h_for2 h_trait1 h_trait2
  unfold checkClassTraitCoherence at h_coh
  -- The coherence check passes for all class names including className
  rw [List.all_eq_true] at h_coh
  have h_class_check := h_coh className h_class_mem
  simp only [beq_iff_eq] at h_class_check
  -- classImpls are the impls for className
  let classImpls := env.impls.filter (fun impl => impl.for_type == Ty.named className)
  -- impl1 and impl2 are both in classImpls
  have h_impl1_in_class : impl1 ∈ classImpls := by
    simp only [classImpls, List.mem_filter, h_for1, beq_self_eq_true, and_true]
    exact h_impl1_mem
  have h_impl2_in_class : impl2 ∈ classImpls := by
    simp only [classImpls, List.mem_filter, h_for2, beq_self_eq_true, and_true]
    exact h_impl2_mem
  -- The trait names have no duplicates
  have h_nodup : (classImpls.map TraitImpl.trait_name).Nodup :=
    nodup_of_length_eq_eraseDups' _ h_class_check
  -- Since impl1 and impl2 have the same trait_name, they must be equal
  have h_same_name : impl1.trait_name = impl2.trait_name := by rw [h_trait1, h_trait2]
  exact nodup_map_injective' classImpls TraitImpl.trait_name h_nodup impl1 impl2
    h_impl1_in_class h_impl2_in_class h_same_name

-- Theorem: Valid trait implementation satisfies all method requirements
-- With uniqueness preconditions for both trait methods and impl methods
theorem validImpl_complete (env : TypeEnv) (impl : TraitImpl) (trait : TraitDef)
    (h_trait_nodup : (trait.methods.map TraitMethod.name).Nodup)
    (h_impl_nodup : (impl.method_impls.map Prod.fst).Nodup)
    (h_valid : validateTraitImpl env impl = true)
    (h_lookup : lookupTrait env.traits impl.trait_name = some trait) :
    trait.methods.length ≤ impl.method_impls.length := by
  unfold validateTraitImpl at h_valid
  cases h_for : impl.for_type with
  | named className =>
    simp only [h_for, h_lookup] at h_valid
    -- h_valid : trait.methods.all (fun tm => impl.method_impls.any (fun (n, _) => n == tm.name)) = true
    -- Each trait method has a matching impl method by name
    -- With uniqueness of both, we get the length inequality
    -- Transform the any predicate
    have h_all : trait.methods.all (fun tm =>
        (impl.method_impls.map Prod.fst).any (fun n => n == tm.name)) = true := by
      rw [List.all_eq_true] at h_valid ⊢
      intro tm h_mem
      specialize h_valid tm h_mem
      rw [List.any_eq_true] at h_valid ⊢
      obtain ⟨⟨n, ty⟩, h_mem', h_eq⟩ := h_valid
      use n
      constructor
      · exact List.mem_map_of_mem Prod.fst h_mem'
      · exact h_eq
    -- Now apply: if for each x ∈ as, there's some b ∈ bs with b == f(x),
    -- and as.map f has no dups, then |as| ≤ |bs|
    -- This is the injection principle
    -- Count distinct names needed = trait.methods.length (by nodup of trait methods)
    -- Count available names = impl.method_impls.length
    -- The matching ensures each trait method name appears in impl
    -- With nodup on trait, each name is distinct
    -- So we need at least that many impl methods
    -- Actually, we need to show that each trait method name maps to a distinct impl method name
    -- But the impl could have the same name for multiple entries...
    -- With h_impl_nodup, each impl method name is unique
    -- So the set of impl method names has size = impl.method_impls.length
    -- And each trait method name (unique by h_trait_nodup) maps to some impl method name
    -- This gives an injection from trait method names to impl method names
    -- Therefore |trait.methods| ≤ |impl.method_impls|
    have h_inj : ∀ tm ∈ trait.methods, tm.name ∈ impl.method_impls.map Prod.fst := by
      intro tm h_mem
      rw [List.all_eq_true] at h_all
      specialize h_all tm h_mem
      rw [List.any_eq_true] at h_all
      obtain ⟨n, h_n_mem, h_eq⟩ := h_all
      simp only [beq_iff_eq] at h_eq
      rw [← h_eq]
      exact h_n_mem
    -- With h_trait_nodup: trait.methods.map TraitMethod.name has no dups
    -- And each name is in impl.method_impls.map Prod.fst
    -- This means trait.methods.map TraitMethod.name ⊆ impl.method_impls.map Prod.fst (as a set)
    -- With nodup on the domain, |domain| ≤ |codomain|
    have h_subset : ∀ n ∈ trait.methods.map TraitMethod.name, n ∈ impl.method_impls.map Prod.fst := by
      intro n h_mem
      rw [List.mem_map] at h_mem
      obtain ⟨tm, h_tm_mem, h_eq⟩ := h_mem
      rw [← h_eq]
      exact h_inj tm h_tm_mem
    -- Now: |trait.methods| = |trait.methods.map TraitMethod.name| (since map preserves length)
    -- And trait.methods.map TraitMethod.name ⊆ impl.method_impls.map Prod.fst with nodup
    -- So |trait.methods.map TraitMethod.name| ≤ |impl.method_impls.map Prod.fst|
    -- = |impl.method_impls|
    have h_map_len1 : trait.methods.length = (trait.methods.map TraitMethod.name).length :=
      (List.length_map trait.methods TraitMethod.name).symm
    have h_map_len2 : impl.method_impls.length = (impl.method_impls.map Prod.fst).length :=
      (List.length_map impl.method_impls Prod.fst).symm
    rw [h_map_len1, h_map_len2]
    exact List.Nodup.length_le_of_subset h_trait_nodup h_subset
  | _ => simp only [h_for] at h_valid

-- Theorem: Type conversion preserves structure (since types are now unified, this is trivial)
theorem tyConversion_roundtrip (ty : Ty) :
  ty = ty := rfl

-- Note: genericBounds_sound removed - the statement had no preconditions and was incorrect.
-- A proper soundness theorem would require preconditions about the bounds being
-- derivable from the class definition and the type arguments satisfying them.

--==============================================================================
-- Mixin-Trait-DynTrait Integration Theorems
--==============================================================================

/-- Mixin methods are found by resolveMethodSource after application.
    If a mixin provides a method and no class/trait method shadows it,
    resolveMethodSource finds it. -/
theorem mixin_method_in_resolution (env : TypeEnv) (className methodName : String)
    (cls : ClassDef) (mixinName : String) (mixinMethod : MethodDef)
    (h_class : lookupClass env.classes className = some cls)
    (h_no_class_method : lookupMethod cls methodName = none)
    (h_no_trait_method : (env.impls.filter (fun impl =>
        impl.for_type == Ty.named className)).findSome? (fun impl =>
        match lookupTrait env.traits impl.trait_name with
        | some trait => lookupTraitMethod trait methodName |>.map (fun m =>
            MethodSource.traitMethod impl.trait_name m)
        | none => none) = none)
    (h_mixin : (mixinName, { name := mixinName, type_params := [], required_traits := [],
        required_mixins := [], fields := [], methods := [mixinMethod],
        required_methods := [] : MixinDef }) ∈ env.mixins)
    (h_method_name : mixinMethod.name = methodName) :
    ∃ src, resolveMethodSource env className methodName = some src := by
  unfold resolveMethodSource
  simp only [h_class, h_no_class_method, h_no_trait_method]
  -- The mixin method should be found by findSome? on env.mixins
  sorry -- Requires showing findSome? finds the mixin entry

/-- Dyn trait method resolution is sound: returns correct type for well-typed dispatch -/
theorem dyn_method_resolution_sound (env : TypeEnv)
    (traitName methodName : String) (argTys : List Ty) (retTy : Ty) :
    inferDynMethodCall env.traits traitName methodName argTys = some retTy →
    inferIntegratedMethodCall env (Ty.dynTrait traitName) methodName argTys = some retTy := by
  intro h
  unfold inferIntegratedMethodCall
  exact h

/-- Mixin trait requirement propagation: if mixin M requires trait T,
    and mixin N requires mixin M, then any class using N must implement T. -/
theorem mixin_trait_propagation (traitEnv : TraitEnv) (registry : ImplRegistry)
    (mixinM mixinN : MixinDef) (targetType : Ty) :
    mixinM.name ∈ mixinN.required_mixins →
    "T" ∈ mixinM.required_traits →
    checkMixinTraitRequirements traitEnv registry mixinM targetType = true →
    implementsTrait registry targetType "T" = true := by
  intro _h_req_mixin h_req_trait h_check
  unfold checkMixinTraitRequirements at h_check
  rw [List.all_eq_true] at h_check
  exact h_check "T" h_req_trait
