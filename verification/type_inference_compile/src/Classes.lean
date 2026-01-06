/-
  Classes.lean - Formal verification of class type inference

  This module formalizes type inference for classes with:
  - Class definitions with typed fields
  - Constructor type checking
  - Field access type inference
  - Method calls with self parameter
  - Class inheritance and subtyping
  - Generic classes with type parameters
-/

-- Type variables for polymorphism
inductive TyVar where
  | mk (id : Nat)
  deriving DecidableEq, Repr

-- Types in the class system
inductive Ty where
  | int                            -- Int type
  | bool                           -- Bool type
  | str                            -- Str type
  | var (v : TyVar)               -- Type variable
  | named (name : String)          -- Named type (class name)
  | arrow (params : List Ty) (ret : Ty)  -- Function type
  | generic (name : String) (args : List Ty)  -- Generic type: Class[T, U]
  deriving BEq, DecidableEq, Repr

-- Field definition in a class
structure FieldDef where
  name : String
  ty : Ty
  deriving DecidableEq, Repr

-- Method definition in a class
structure MethodDef where
  name : String
  self_ty : Ty                     -- Type of self parameter
  params : List Ty                 -- Other parameter types
  ret : Ty                         -- Return type
  deriving DecidableEq, Repr

-- Class definition
structure ClassDef where
  name : String
  type_params : List TyVar         -- Generic type parameters
  fields : List FieldDef           -- Class fields
  methods : List MethodDef         -- Class methods
  parent : Option String           -- Parent class name (for inheritance)
  deriving DecidableEq, Repr

-- Type environment mapping class names to definitions
def ClassEnv := List (String × ClassDef)

-- Field environment mapping variable names to types
def FieldEnv := List (String × Ty)

-- Look up a class definition
def lookupClass (env : ClassEnv) (name : String) : Option ClassDef :=
  env.find? (fun (n, _) => n == name) |>.map (·.2)

-- Look up a field type in a class
def lookupField (cls : ClassDef) (fieldName : String) : Option Ty :=
  cls.fields.find? (fun f => f.name == fieldName) |>.map (·.ty)

-- Look up a method in a class
def lookupMethod (cls : ClassDef) (methodName : String) : Option MethodDef :=
  cls.methods.find? (fun m => m.name == methodName)

-- Substitution for type variables
def Subst := List (TyVar × Ty)

-- Apply substitution to a type
def applySubst (subst : Subst) (ty : Ty) : Ty :=
  match ty with
  | Ty.var v =>
      match subst.find? (fun (v', _) => v == v') with
      | some (_, ty') => ty'
      | none => Ty.var v
  | Ty.arrow params ret =>
      Ty.arrow (params.map (applySubst subst)) (applySubst subst ret)
  | Ty.generic name args =>
      Ty.generic name (args.map (applySubst subst))
  | ty => ty

-- Instantiate a generic class with concrete type arguments
-- Example: instantiate Class[T, U] with [Int, Str] -> Class[Int, Str]
def instantiateClass (cls : ClassDef) (typeArgs : List Ty) : Option ClassDef :=
  if cls.type_params.length != typeArgs.length then
    none
  else
    let subst := cls.type_params.zip typeArgs
    some {
      name := cls.name
      type_params := []
      fields := cls.fields.map (fun f => { f with ty := applySubst subst f.ty })
      methods := cls.methods.map (fun m => {
        m with
        self_ty := applySubst subst m.self_ty
        params := m.params.map (applySubst subst)
        ret := applySubst subst m.ret
      })
      parent := cls.parent
    }

-- Check if ty1 is a subtype of ty2
-- For now, this is just equality; can be extended for inheritance
partial def isSubtype (env : ClassEnv) (ty1 ty2 : Ty) : Bool :=
  match ty1, ty2 with
  | Ty.named name1, Ty.named name2 =>
      if name1 == name2 then
        true
      else
        -- Check inheritance chain
        match lookupClass env name1 with
        | some cls =>
            match cls.parent with
            | some parent => isSubtype env (Ty.named parent) ty2
            | none => false
        | none => false
  | _, _ => ty1 == ty2

-- Type inference for field access: obj.field
-- Given: class type, field name
-- Returns: field type if found
def inferFieldAccess (env : ClassEnv) (objTy : Ty) (fieldName : String) : Option Ty :=
  match objTy with
  | Ty.named className =>
      match lookupClass env className with
      | some cls => lookupField cls fieldName
      | none => none
  | Ty.generic className typeArgs =>
      match lookupClass env className with
      | some cls =>
          match instantiateClass cls typeArgs with
          | some instantiated => lookupField instantiated fieldName
          | none => none
      | none => none
  | _ => none

-- Type check constructor call: ClassName { field1: val1, field2: val2 }
-- Given: class name, field assignments (field name -> value type)
-- Returns: class type if all fields match
def checkConstructor (env : ClassEnv) (className : String) (fieldAssigns : List (String × Ty)) : Option Ty :=
  match lookupClass env className with
  | some cls =>
      -- Check that all class fields are provided with correct types
      let allFieldsMatch := cls.fields.all (fun fieldDef =>
        match fieldAssigns.find? (fun (name, _) => name == fieldDef.name) with
        | some (_, ty) => ty == fieldDef.ty
        | none => false
      )
      if allFieldsMatch && fieldAssigns.length == cls.fields.length then
        some (Ty.named className)
      else
        none
  | none => none

-- Type inference for method call: obj.method(arg1, arg2, ...)
-- Given: object type, method name, argument types
-- Returns: return type if method exists and arguments match
def inferMethodCall (env : ClassEnv) (objTy : Ty) (methodName : String) (argTys : List Ty) : Option Ty :=
  match objTy with
  | Ty.named className =>
      match lookupClass env className with
      | some cls =>
          match lookupMethod cls methodName with
          | some method =>
              -- Check that self type matches and arguments match
              if isSubtype env objTy method.self_ty && method.params == argTys then
                some method.ret
              else
                none
          | none => none
      | none => none
  | Ty.generic className typeArgs =>
      match lookupClass env className with
      | some cls =>
          match instantiateClass cls typeArgs with
          | some instantiated =>
              match lookupMethod instantiated methodName with
              | some method =>
                  if method.params == argTys then
                    some method.ret
                  else
                    none
              | none => none
          | none => none
      | none => none
  | _ => none

--==============================================================================
-- Theorems and Properties
--==============================================================================

-- Theorem: Field access is deterministic
theorem fieldAccess_deterministic (env : ClassEnv) (objTy : Ty) (fieldName : String) (ty1 ty2 : Ty) :
  inferFieldAccess env objTy fieldName = some ty1 →
  inferFieldAccess env objTy fieldName = some ty2 →
  ty1 = ty2 := by
  intro h1 h2
  simp [inferFieldAccess] at h1 h2
  cases objTy <;> try (simp at h1; contradiction)
  case named className =>
    cases hLookup : lookupClass env className <;> simp [hLookup] at h1 h2
    case some cls =>
      cases hField : lookupField cls fieldName <;> simp [hField] at h1 h2
      case some fieldTy =>
        cases h1
        cases h2
        rfl
  case generic className typeArgs =>
    cases hLookup : lookupClass env className <;> simp [hLookup] at h1 h2
    case some cls =>
      cases hInst : instantiateClass cls typeArgs <;> simp [hInst] at h1 h2
      case some instantiated =>
        cases hField : lookupField instantiated fieldName <;> simp [hField] at h1 h2
        case some fieldTy =>
          cases h1
          cases h2
          rfl

-- Theorem: Constructor type checking is sound
-- If constructor succeeds, the resulting type is the class type
theorem constructor_sound (env : ClassEnv) (className : String) (fieldAssigns : List (String × Ty)) (ty : Ty) :
  checkConstructor env className fieldAssigns = some ty →
  ty = Ty.named className := by
  intro h
  simp [checkConstructor] at h
  cases hLookup : lookupClass env className <;> simp [hLookup] at h
  case some cls =>
    split at h <;> try contradiction
    cases h
    rfl

-- Theorem: Method call inference is deterministic
theorem methodCall_deterministic (env : ClassEnv) (objTy : Ty) (methodName : String) (argTys : List Ty) (retTy1 retTy2 : Ty) :
  inferMethodCall env objTy methodName argTys = some retTy1 →
  inferMethodCall env objTy methodName argTys = some retTy2 →
  retTy1 = retTy2 := by
  intro h1 h2
  simp [inferMethodCall] at h1 h2
  cases objTy <;> try (simp at h1; contradiction)
  case named className =>
    cases hLookup : lookupClass env className <;> simp [hLookup] at h1 h2
    case some cls =>
      cases hMethod : lookupMethod cls methodName <;> simp [hMethod] at h1 h2
      case some method =>
        split at h1 <;> try (simp at h1; contradiction)
        split at h2 <;> try (simp at h2; contradiction)
        cases h1
        cases h2
        rfl
  case generic className typeArgs =>
    cases hLookup : lookupClass env className <;> simp [hLookup] at h1 h2
    case some cls =>
      cases hInst : instantiateClass cls typeArgs <;> simp [hInst] at h1 h2
      case some instantiated =>
        cases hMethod : lookupMethod instantiated methodName <;> simp [hMethod] at h1 h2
        case some method =>
          split at h1 <;> try (simp at h1; contradiction)
          split at h2 <;> try (simp at h2; contradiction)
          cases h1
          cases h2
          rfl

-- Theorem: Subtyping is reflexive
theorem subtype_reflexive (env : ClassEnv) (ty : Ty) :
  isSubtype env ty ty = true := by
  cases ty <;> simp [isSubtype]
  case named name =>
    rfl
  case var v =>
    rfl
  case int =>
    rfl
  case bool =>
    rfl
  case str =>
    rfl

-- Theorem: Subtyping is transitive
-- If A <: B and B <: C, then A <: C
theorem subtype_transitive (env : ClassEnv) (ty1 ty2 ty3 : Ty) :
  isSubtype env ty1 ty2 = true →
  isSubtype env ty2 ty3 = true →
  isSubtype env ty1 ty3 = true := by
  intro h12 h23
  cases ty1 <;> cases ty2 <;> cases ty3 <;> try (simp [isSubtype] at h12 h23; contradiction)
  case named.named.named name1 name2 name3 =>
    simp [isSubtype] at h12 h23 ⊢
    if h : name1 == name2 then
      simp [h] at h12
      if h' : name2 == name3 then
        simp [h']
      else
        simp [h'] at h23
        cases hLookup : lookupClass env name2 <;> simp [hLookup] at h23
        case some cls =>
          cases cls.parent <;> simp at h23
          case some parent =>
            sorry  -- Would need to reason about inheritance chain
    else
      simp [h] at h12
      sorry  -- Would need to reason about inheritance chain
  case _ => simp [isSubtype]
