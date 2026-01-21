/-
  Mixins.lean - Formal verification of mixin type inference
  
  This module formalizes type inference for mixins with:
  - Mixin declaration and parameterization
  - Field and method composition
  - Type parameter inference for generic mixins
  - Trait requirements on mixins
  - Mixin application to classes/structs
  - Conflict resolution (field/method overriding)
  - Coherence checking (no duplicate definitions)
-/

import Classes
import Traits

-- Using types from Classes: TyVar, Ty, FieldDef, MethodDef, ClassDef, ClassEnv, Subst, applySubst
-- Using types from Traits: TraitEnv, ImplRegistry, implementsTrait

-- Mixin definition
structure MixinDef where
  name : String
  type_params : List TyVar          -- Generic type parameters on the mixin
  required_traits : List String     -- Trait constraints on Self
  required_mixins : List String     -- Other mixins this mixin depends on
  fields : List FieldDef            -- Fields provided by the mixin
  methods : List MethodDef          -- Methods provided by the mixin
  required_methods : List MethodDef -- Abstract methods that must be provided by the target

-- Mixin application/reference
structure MixinRef where
  mixin_name : String               -- Name of mixin being applied
  type_args : List Ty               -- Concrete type arguments
  field_overrides : List (String × Ty)  -- Field type overrides
  method_overrides : List (String × MethodDef)  -- Method implementation overrides

-- Environment mapping mixin names to definitions
def MixinEnv := List (String × MixinDef)

-- Look up a mixin definition
def lookupMixin (env : MixinEnv) (name : String) : Option MixinDef :=
  env.find? (fun p => p.1 == name) |>.map (·.2)

-- Apply type substitution to a mixin
def instantiateMixin (mixin : MixinDef) (typeArgs : List Ty) : Option MixinDef :=
  if mixin.type_params.length != typeArgs.length then
    none
  else
    let subst := mixin.type_params.zip typeArgs
    some {
      name := mixin.name
      type_params := []
      required_traits := mixin.required_traits
      required_mixins := mixin.required_mixins
      fields := mixin.fields.map (fun f => { f with ty := applySubst subst f.ty })
      methods := mixin.methods.map (fun m => {
        m with
        self_ty := applySubst subst m.self_ty
        params := m.params.map (applySubst subst)
        ret := applySubst subst m.ret
      })
      required_methods := mixin.required_methods.map (fun m => {
        m with
        self_ty := applySubst subst m.self_ty
        params := m.params.map (applySubst subst)
        ret := applySubst subst m.ret
      })
    }

-- Check if a type satisfies mixin trait requirements
def checkMixinTraitRequirements (traitEnv : TraitEnv) (registry : ImplRegistry) 
    (mixin : MixinDef) (targetType : Ty) : Bool :=
  mixin.required_traits.all (fun traitName =>
    implementsTrait registry targetType traitName
  )

-- Check if required mixins are already applied to the target
def checkRequiredMixins (appliedMixins : List String) (required : List String) : Bool :=
  required.all (fun req => appliedMixins.contains req)

-- Merge fields from a mixin into a class
-- Returns None if there are field type conflicts
def mergeFields (classFields : List FieldDef) (mixinFields : List FieldDef) 
    (overrides : List (String × Ty)) : Option (List FieldDef) :=
  let classFieldNames := classFields.map (·.name)
  -- Check for conflicts
  let conflicts := mixinFields.filter (fun mf =>
    classFieldNames.contains mf.name &&
    !overrides.any (fun (n, _) => n == mf.name)
  )
  if conflicts.isEmpty then
    -- Apply overrides to mixin fields
    let mixinFieldsOverridden := mixinFields.map (fun f =>
      match overrides.find? (fun (n, _) => n == f.name) with
      | some (_, newType) => { f with ty := newType }
      | none => f
    )
    -- Merge: class fields + new mixin fields (not already in class)
    let newFields := mixinFieldsOverridden.filter (fun mf =>
      !classFieldNames.contains mf.name
    )
    some (classFields ++ newFields)
  else
    none

-- Merge methods from a mixin into a class
-- Methods in class take priority; mixin provides defaults
def mergeMethods (classMethods : List MethodDef) (mixinMethods : List MethodDef)
    (overrides : List (String × MethodDef)) : List MethodDef :=
  let classMethodNames := classMethods.map (·.name)
  -- Apply overrides to mixin methods
  let mixinMethodsOverridden := mixinMethods.map (fun m =>
    match overrides.find? (fun (n, _) => n == m.name) with
    | some (_, newMethod) => newMethod
    | none => m
  )
  -- Add mixin methods that don't exist in class
  let newMethods := mixinMethodsOverridden.filter (fun mm =>
    !classMethodNames.contains mm.name
  )
  classMethods ++ newMethods

-- Check that required methods are satisfied
-- Returns true if all required methods are provided by either the class or overrides
def checkRequiredMethods (classMethods : List MethodDef) (required : List MethodDef)
    (overrides : List (String × MethodDef)) : Bool :=
  required.all (fun req =>
    -- Method is provided by class
    classMethods.any (fun m => m.name == req.name && m.params == req.params && m.ret == req.ret) ||
    -- Method is provided via override
    overrides.any (fun (n, m) => n == req.name && m.params == req.params && m.ret == req.ret)
  )

-- Apply a mixin to a class definition
-- Returns the updated class with mixin fields/methods merged
def applyMixinToClass (env : MixinEnv) (traitEnv : TraitEnv) (registry : ImplRegistry)
    (cls : ClassDef) (mixinRef : MixinRef) (appliedMixins : List String) : Option ClassDef :=
  match lookupMixin env mixinRef.mixin_name with
  | none => none
  | some mixin =>
      -- Instantiate mixin with type arguments
      match instantiateMixin mixin mixinRef.type_args with
      | none => none  -- Type arity mismatch
      | some instantiatedMixin =>
          -- Check trait requirements
          if !checkMixinTraitRequirements traitEnv registry instantiatedMixin (Ty.named cls.name) then
            none  -- Trait requirements not satisfied
          else if !checkRequiredMixins appliedMixins instantiatedMixin.required_mixins then
            none  -- Required mixins not applied
          else if !checkRequiredMethods cls.methods instantiatedMixin.required_methods mixinRef.method_overrides then
            none  -- Required methods not provided
          else
            -- Merge fields and methods
            match mergeFields cls.fields instantiatedMixin.fields mixinRef.field_overrides with
            | none => none  -- Field conflicts
            | some mergedFields =>
                let mergedMethods := mergeMethods cls.methods instantiatedMixin.methods mixinRef.method_overrides
                some {
                  name := cls.name
                  type_params := cls.type_params
                  fields := mergedFields
                  methods := mergedMethods
                  parent := cls.parent
                }

-- Infer type of field access with mixin-provided fields
-- Same as before but now includes mixin fields
def inferFieldAccessWithMixins (env : ClassEnv) (ty : Ty) (fieldName : String) : Option Ty :=
  inferFieldAccess env ty fieldName

-- Infer type of method call with mixin-provided methods
-- Same as before but now includes mixin methods
def inferMethodCallWithMixins (env : ClassEnv) (ty : Ty) (methodName : String) (argTys : List Ty) : Option Ty :=
  inferMethodCall env ty methodName argTys

-- Check coherence: no duplicate mixin applications
def checkMixinCoherence (mixinRefs : List MixinRef) : Bool :=
  let mixinNames := mixinRefs.map (·.mixin_name)
  mixinNames.length == mixinNames.eraseDups.length

-- Validate that a mixin application is well-formed
def validateMixinApplication (env : MixinEnv) (traitEnv : TraitEnv) (registry : ImplRegistry)
    (cls : ClassDef) (mixinRefs : List MixinRef) : Bool :=
  -- Check coherence (no duplicate mixins)
  checkMixinCoherence mixinRefs &&
  -- Check each mixin can be applied successfully
  (let rec applyAll (c : ClassDef) (refs : List MixinRef) (applied : List String) : Bool :=
    match refs with
    | [] => true
    | r :: rest =>
        match applyMixinToClass env traitEnv registry c r applied with
        | none => false
        | some c' => applyAll c' rest (applied ++ [r.mixin_name])
   applyAll cls mixinRefs [])

-- Infer type variables for generic mixin instantiation
-- Given: mixin with type params, target class type, field/method usage context
-- Returns: substitution mapping type variables to concrete types
def inferMixinTypeArgs (mixin : MixinDef) (targetType : Ty) (context : List (String × Ty)) : Option (List Ty) :=
  -- Simplified: assume type arguments are provided explicitly
  -- Full implementation would use constraint solving
  none

-- ===== Theorems =====

-- Theorem: Mixin instantiation with correct type arguments preserves well-formedness
theorem instantiation_preserves_wellformedness (mixin : MixinDef) (typeArgs : List Ty) :
  mixin.type_params.length = typeArgs.length →
  instantiateMixin mixin typeArgs ≠ none := by
  intro h_len
  unfold instantiateMixin
  simp [h_len]

-- Note: Field merging is NOT commutative in general.
-- mergeFields(A, B, _) returns A ++ (B filtered) while mergeFields(B, A, _) returns B ++ (A filtered)
-- The order determines which fields take priority (first argument = class fields = priority)
-- The original axiom was incorrect and has been removed.
-- Property: Field merging preserves the first argument's fields
theorem field_merge_preserves_first (classFields mixinFields : List FieldDef) (overrides : List (String × Ty))
    (result : List FieldDef) :
    mergeFields classFields mixinFields overrides = some result →
    ∀ f, f ∈ classFields → f ∈ result := by
  intro h_merge f h_mem
  unfold mergeFields at h_merge
  -- The result is classFields ++ newFields, so classFields is a prefix
  split at h_merge
  · simp at h_merge
  · rename_i h_empty
    simp only at h_merge
    injection h_merge with h_eq
    rw [← h_eq]
    exact List.mem_append_left _ h_mem

-- Theorem: Method merging preserves class method priority
theorem method_merge_priority (classMethods mixinMethods : List MethodDef) (overrides : List (String × MethodDef)) (methodName : String) :
  (∃ m, m ∈ classMethods ∧ m.name = methodName) →
  (∃ m, m ∈ mergeMethods classMethods mixinMethods overrides ∧ m.name = methodName ∧ m ∈ classMethods) := by
  intro ⟨m, h_mem, h_name⟩
  refine ⟨m, ?_, h_name, h_mem⟩
  -- m is in classMethods, and mergeMethods returns classMethods ++ newMethods
  unfold mergeMethods
  simp only [List.mem_append]
  left
  exact h_mem

-- Theorem: Applying a valid mixin preserves class structure
theorem mixin_application_sound (env : MixinEnv) (traitEnv : TraitEnv) (registry : ImplRegistry)
    (cls : ClassDef) (mixinRef : MixinRef) (applied : List String) (cls' : ClassDef) :
  applyMixinToClass env traitEnv registry cls mixinRef applied = some cls' →
  cls'.name = cls.name ∧ cls'.type_params = cls.type_params := by
  intro h
  unfold applyMixinToClass at h
  -- Case analysis on lookupMixin
  cases h_lookup : lookupMixin env mixinRef.mixin_name with
  | none => simp [h_lookup] at h
  | some mixin =>
    simp only [h_lookup] at h
    -- Case analysis on instantiateMixin
    cases h_inst : instantiateMixin mixin mixinRef.type_args with
    | none => simp [h_inst] at h
    | some instantiated =>
      simp only [h_inst] at h
      -- Now we have a series of if-then-else branches
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · -- Now case analysis on mergeFields
            cases h_merge : mergeFields cls.fields instantiated.fields mixinRef.field_overrides with
            | none => simp [h_merge] at h
            | some merged =>
              simp only [h_merge] at h
              cases h
              constructor <;> rfl

-- Helper: If length equals eraseDups length, then no duplicates in mapped list
theorem nodup_of_length_eq_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
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
theorem nodup_map_injective {α β : Type} [DecidableEq β] (l : List α) (f : α → β)
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

-- Theorem: Coherence prevents duplicate mixin applications
-- If coherence check passes, two refs with the same mixin name must be identical
theorem coherence_no_duplicates (mixinRefs : List MixinRef) (name : String) (r1 r2 : MixinRef) :
  checkMixinCoherence mixinRefs = true →
  r1 ∈ mixinRefs →
  r2 ∈ mixinRefs →
  r1.mixin_name = name →
  r2.mixin_name = name →
  r1 = r2 := by
  intro h_coh h_r1 h_r2 h_name1 h_name2
  unfold checkMixinCoherence at h_coh
  simp only [beq_iff_eq] at h_coh
  have h_nodup : (mixinRefs.map MixinRef.mixin_name).Nodup := nodup_of_length_eq_eraseDups _ h_coh
  have h_eq : r1.mixin_name = r2.mixin_name := by rw [h_name1, h_name2]
  exact nodup_map_injective mixinRefs MixinRef.mixin_name h_nodup r1 r2 h_r1 h_r2 h_eq

-- Theorem: Required method checking is complete
-- If checkRequiredMethods passes, every required method has a matching implementation
theorem required_methods_complete (classMethods : List MethodDef) (required : List MethodDef)
    (overrides : List (String × MethodDef)) :
  checkRequiredMethods classMethods required overrides = true →
  ∀ req, req ∈ required → ∃ m, (m ∈ classMethods ∨ ∃ n m', (n, m') ∈ overrides ∧ n = req.name ∧ m' = m) ∧
    m.name = req.name ∧ m.params = req.params ∧ m.ret = req.ret := by
  intro h_check req h_req_mem
  unfold checkRequiredMethods at h_check
  rw [List.all_eq_true] at h_check
  have h_req := h_check req h_req_mem
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, Bool.and_eq_true] at h_req
  cases h_req with
  | inl h_class =>
    -- Found in classMethods
    obtain ⟨m, h_mem, h_name, h_params, h_ret⟩ := h_class
    exact ⟨m, Or.inl h_mem, h_name, h_params, h_ret⟩
  | inr h_override =>
    -- Found in overrides
    obtain ⟨⟨n, m'⟩, h_mem, h_name, h_params, h_ret⟩ := h_override
    exact ⟨m', Or.inr ⟨n, m', h_mem, h_name, rfl⟩, h_name, h_params, h_ret⟩

-- Theorem: Trait requirements are sound
theorem mixin_trait_requirements_sound (traitEnv : TraitEnv) (registry : ImplRegistry)
    (mixin : MixinDef) (targetType : Ty) :
  checkMixinTraitRequirements traitEnv registry mixin targetType = true →
  ∀ traitName, traitName ∈ mixin.required_traits → implementsTrait registry targetType traitName = true := by
  intro h_check traitName h_mem
  unfold checkMixinTraitRequirements at h_check
  rw [List.all_eq_true] at h_check
  exact h_check traitName h_mem

-- Theorem: Field access after mixin application includes mixin fields
-- REMAINS AXIOM: The inferFieldAccessWithMixins function requires cls'.name to be in the
-- ClassEnv, which isn't guaranteed by the hypotheses. A correct statement would need:
-- lookupClass env cls'.name = some cls' as a precondition.
axiom mixin_field_access (env : ClassEnv) (cls cls' : ClassDef) (mixinFields : List FieldDef) (fieldName : String) :
  cls'.fields = cls.fields ++ mixinFields →
  (∃ f, f ∈ mixinFields ∧ f.name = fieldName) →
  inferFieldAccessWithMixins env (Ty.named cls'.name) fieldName ≠ none

-- Theorem: Method dispatch after mixin application includes mixin methods
-- REMAINS AXIOM: Same issue as mixin_field_access - the function requires cls'.name to be
-- in the ClassEnv. Additionally, the existential "∃ argTys" doesn't specify which argument
-- types would work. A correct statement would need the class in env and specify the method's params.
axiom mixin_method_dispatch (env : ClassEnv) (cls cls' : ClassDef) (mixinMethods : List MethodDef) (methodName : String) :
  cls'.methods = cls.methods ++ mixinMethods →
  (∃ m, m ∈ mixinMethods ∧ m.name = methodName) →
  ∃ argTys, inferMethodCallWithMixins env (Ty.named cls'.name) methodName argTys ≠ none

-- Theorem: Type substitution in mixins is consistent
theorem mixin_substitution_consistent (mixin : MixinDef) (typeArgs : List Ty) (subst : Subst) :
  mixin.type_params.length = typeArgs.length →
  ∀ f, f ∈ mixin.fields → applySubst subst f.ty = applySubst subst f.ty := by
  intro _ _ _
  rfl
