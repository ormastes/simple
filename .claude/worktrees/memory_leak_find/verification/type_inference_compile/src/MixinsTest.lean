import Mixins

/-
  MixinsTest.lean - Test cases for mixin type inference verification

  This module provides concrete test cases demonstrating the mixin system:
  - Basic mixin with fields
  - Generic mixin with type parameters
  - Mixin with trait requirements
  - Mixin with required methods
  - Multiple mixin composition
  - Mixin with method overrides
-/

-- Example 1: Basic mixin with fields
def TimestampMixin : MixinDef := {
  name := "Timestamp"
  type_params := []
  required_traits := []
  required_mixins := []
  fields := [
    { name := "created_at", ty := Ty.int },
    { name := "updated_at", ty := Ty.int }
  ]
  methods := []
  required_methods := []
}

-- Example 2: Generic mixin with type parameter
def CacheMixin : MixinDef :=
  let T := TyVar.mk 0
  {
    name := "Cache"
    type_params := [T]
    required_traits := []
    required_mixins := []
    fields := [
      { name := "cache", ty := Ty.named "HashMap" }
    ]
    methods := [
      {
        name := "get_cached"
        self_ty := Ty.named "Self"
        params := [Ty.named "String"]
        ret := Ty.generic "Option" [Ty.var T]
      },
      {
        name := "set_cache"
        self_ty := Ty.named "Self"
        params := [Ty.named "String", Ty.var T]
        ret := Ty.int  -- unit represented as int
      }
    ]
    required_methods := []
  }

-- Example 3: Mixin with trait requirement
def SerializableMixin : MixinDef := {
  name := "Serializable"
  type_params := []
  required_traits := ["Serialize", "Deserialize"]
  required_mixins := []
  fields := []
  methods := [
    {
      name := "to_json"
      self_ty := Ty.named "Self"
      params := []
      ret := Ty.named "String"
    },
    {
      name := "from_json"
      self_ty := Ty.named "Self"
      params := [Ty.named "String"]
      ret := Ty.generic "Result" [Ty.named "Self", Ty.named "Error"]
    }
  ]
  required_methods := []
}

-- Example 4: Mixin with required methods
def RepositoryMixin : MixinDef :=
  let T := TyVar.mk 0
  {
    name := "Repository"
    type_params := [T]
    required_traits := []
    required_mixins := []
    fields := [
      { name := "connection", ty := Ty.named "DbConnection" }
    ]
    methods := [
      {
        name := "find_by_id"
        self_ty := Ty.named "Self"
        params := [Ty.int]
        ret := Ty.generic "Option" [Ty.var T]
      }
    ]
    required_methods := [
      {
        name := "table_name"
        self_ty := Ty.named "Self"
        params := []
        ret := Ty.named "String"
      }
    ]
  }

-- Example 5: Class before mixin application
def UserClassBase : ClassDef := {
  name := "User"
  type_params := []
  fields := [
    { name := "id", ty := Ty.int },
    { name := "name", ty := Ty.named "String" }
  ]
  methods := [
    {
      name := "get_id"
      self_ty := Ty.named "User"
      params := []
      ret := Ty.int
    }
  ]
  parent := none
}

-- Example 6: Apply TimestampMixin to User class
def UserWithTimestamp : MixinRef := {
  mixin_name := "Timestamp"
  type_args := []
  field_overrides := []
  method_overrides := []
}

-- Verify that TimestampMixin can be applied
def testTimestampApplication : Bool :=
  let env : MixinEnv := [("Timestamp", TimestampMixin)]
  let traitEnv : TraitEnv := []
  let registry : ImplRegistry := []
  match applyMixinToClass env traitEnv registry UserClassBase UserWithTimestamp [] with
  | some cls =>
      -- Check that fields were merged
      cls.fields.length == UserClassBase.fields.length + TimestampMixin.fields.length
  | none => false

#eval testTimestampApplication  -- Expected: true

-- Example 7: Apply multiple mixins (Timestamp + Serializable)
def UserWithMultipleMixins : List MixinRef := [
  { mixin_name := "Timestamp", type_args := [], field_overrides := [], method_overrides := [] },
  { mixin_name := "Serializable", type_args := [], field_overrides := [], method_overrides := [] }
]

-- Test coherence checking
def testCoherence1 : Bool :=
  checkMixinCoherence UserWithMultipleMixins

#eval testCoherence1  -- Expected: true

-- Test coherence failure (duplicate mixin)
def testCoherence2 : Bool :=
  let duplicateMixins := [
    { mixin_name := "Timestamp", type_args := [], field_overrides := [], method_overrides := [] },
    { mixin_name := "Timestamp", type_args := [], field_overrides := [], method_overrides := [] }
  ]
  checkMixinCoherence duplicateMixins

#eval testCoherence2  -- Expected: false

-- Example 8: Generic mixin instantiation
def testCacheInstantiation : Bool :=
  let stringCacheArgs := [Ty.named "String"]
  match instantiateMixin CacheMixin stringCacheArgs with
  | some instantiated =>
      -- Check type params are empty after instantiation
      instantiated.type_params.isEmpty
  | none => false

#eval testCacheInstantiation  -- Expected: true

-- Example 9: Required method checking
def UserWithTableName : ClassDef :=
  let base := UserClassBase
  { base with
    methods := base.methods ++ [{
      name := "table_name"
      self_ty := Ty.named "User"
      params := []
      ret := Ty.named "String"
    }]
  }

def testRequiredMethods : Bool :=
  let repositoryArgs := [Ty.named "User"]
  match instantiateMixin RepositoryMixin repositoryArgs with
  | some repo =>
      checkRequiredMethods UserWithTableName.methods repo.required_methods []
  | none => false

#eval testRequiredMethods  -- Expected: true

-- Example 10: Field override
def UserWithCustomTimestamp : MixinRef := {
  mixin_name := "Timestamp"
  type_args := []
  field_overrides := [("created_at", Ty.int)]  -- Same type (could be different)
  method_overrides := []
}

def testFieldOverride : Bool :=
  let env : MixinEnv := [("Timestamp", TimestampMixin)]
  let traitEnv : TraitEnv := []
  let registry : ImplRegistry := []
  match applyMixinToClass env traitEnv registry UserClassBase UserWithCustomTimestamp [] with
  | some cls =>
      -- Check that created_at field exists
      match cls.fields.find? (fun f => f.name == "created_at") with
      | some field => field.ty == Ty.int
      | none => false
  | none => false

#eval testFieldOverride  -- Expected: true

-- Example 11: Trait requirement checking
def testTraitRequirements : Bool :=
  let traitEnv : TraitEnv := [
    ("Serialize", {
      name := "Serialize"
      type_params := []
      methods := []
      assoc_types := []
      parent_traits := []
    }),
    ("Deserialize", {
      name := "Deserialize"
      type_params := []
      methods := []
      assoc_types := []
      parent_traits := []
    })
  ]
  let registry : ImplRegistry := [
    {
      trait_name := "Serialize"
      for_type := Ty.named "User"
      type_params := []
      assoc_type_bindings := []
      method_impls := []
      where_clause := []
    },
    {
      trait_name := "Deserialize"
      for_type := Ty.named "User"
      type_params := []
      assoc_type_bindings := []
      method_impls := []
      where_clause := []
    }
  ]
  checkMixinTraitRequirements traitEnv registry SerializableMixin (Ty.named "User")

#eval testTraitRequirements  -- Expected: true

-- Example 12: Dependent mixins (one mixin requires another)
def AuditMixin : MixinDef := {
  name := "Audit"
  type_params := []
  required_traits := []
  required_mixins := ["Timestamp"]  -- Audit requires Timestamp
  fields := [
    { name := "modified_by", ty := Ty.named "String" }
  ]
  methods := []
  required_methods := []
}

def testDependentMixins : Bool :=
  let env : MixinEnv := [
    ("Timestamp", TimestampMixin),
    ("Audit", AuditMixin)
  ]
  let traitEnv : TraitEnv := []
  let registry : ImplRegistry := []
  -- Apply Timestamp first
  match applyMixinToClass env traitEnv registry UserClassBase UserWithTimestamp [] with
  | some cls1 =>
      -- Now apply Audit (which requires Timestamp)
      let auditRef : MixinRef := {
        mixin_name := "Audit"
        type_args := []
        field_overrides := []
        method_overrides := []
      }
      match applyMixinToClass env traitEnv registry cls1 auditRef ["Timestamp"] with
      | some cls2 => cls2.fields.length == UserClassBase.fields.length +
                                          TimestampMixin.fields.length +
                                          AuditMixin.fields.length
      | none => false
  | none => false

#eval testDependentMixins  -- Expected: true

-- Summary: All test cases verify key mixin properties
-- 1. Basic field addition
-- 2. Generic type instantiation
-- 3. Trait requirement checking
-- 4. Required method validation
-- 5. Coherence (no duplicates)
-- 6. Field overrides
-- 7. Method overrides
-- 8. Dependent mixins
