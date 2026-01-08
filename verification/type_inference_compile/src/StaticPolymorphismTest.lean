/-
  StaticPolymorphismTest.lean - Test cases for static polymorphism verification
  
  This module provides concrete test cases demonstrating:
  - Static dispatch with bind static
  - Dynamic dispatch (default)
  - Sized constraint checking
  - Vtable generation
  - Monomorphization
  - Performance properties
-/

import StaticPolymorphism

-- Example 1: Static dispatch with single trait bound
def DrawableTrait : TraitDef := {
  name := "Drawable"
  type_params := []
  methods := [{
    name := "draw"
    self_ty := Ty.named "Self"
    params := []
    ret := Ty.int
  }]
  assoc_types := []
  parent_traits := []
}

def CircleType : Ty := Ty.named "Circle"

def DrawableImpl : TraitImpl := {
  trait_name := "Drawable"
  for_type := CircleType
  type_params := []
  assoc_type_bindings := []
  method_impls := []
  where_clause := []
}

def staticDrawableConstraint : BindConstraint := {
  dispatch := DispatchMode.static
  trait_bounds := ["Drawable"]
  sized := true
}

def staticDrawableParam : BindParam := {
  name := "obj"
  bind_constraint := staticDrawableConstraint
}

-- Test that Circle satisfies static Drawable constraint
def testStaticDrawable : Bool :=
  let env : BindEnv := {
    trait_env := [("Drawable", DrawableTrait)]
    impl_registry := [DrawableImpl]
    vtable_registry := []
    monomorphized := []
  }
  satisfiesBindConstraint env CircleType staticDrawableConstraint

#eval testStaticDrawable  -- Expected: true

-- Example 2: Dynamic dispatch (default)
def dynamicDrawableConstraint : BindConstraint := {
  dispatch := DispatchMode.dynamic
  trait_bounds := ["Drawable"]
  sized := false  -- Not required for dynamic
}

def dynamicDrawableParam : BindParam := {
  name := "obj"
  bind_constraint := dynamicDrawableConstraint
}

def testDynamicDrawable : Bool :=
  let env : BindEnv := {
    trait_env := [("Drawable", DrawableTrait)]
    impl_registry := [DrawableImpl]
    vtable_registry := []
    monomorphized := []
  }
  let vtable := generateVtable env "Drawable" CircleType
  match vtable with
  | some _ => true
  | none => false

#eval testDynamicDrawable  -- Expected: true

-- Example 3: Default dispatch mode
def testDefaultDispatch : Bool :=
  inferDispatchMode none == DispatchMode.dynamic

#eval testDefaultDispatch  -- Expected: true

-- Example 4: Sized constraint
def testSizedTypes : Bool :=
  isSized (Ty.int) &&
  isSized (Ty.named "String") &&
  isSized (Ty.generic "Vec" [Ty.int])

#eval testSizedTypes  -- Expected: true

-- Example 5: Static dispatch with unsized type should fail
def unsizedType : Ty := Ty.var (TyVar.mk 0)  -- Type variable, not Sized

def testStaticUnsized : Bool :=
  let constraint : BindConstraint := {
    dispatch := DispatchMode.static
    trait_bounds := []
    sized := true
  }
  let env : BindEnv := {
    trait_env := []
    impl_registry := []
    vtable_registry := []
    monomorphized := []
  }
  -- Should fail because type variable is not Sized
  !satisfiesBindConstraint env unsizedType constraint

#eval testStaticUnsized  -- Expected: true (constraint not satisfied)

-- Example 6: Multiple trait bounds
def CloneTrait : TraitDef := {
  name := "Clone"
  type_params := []
  methods := [{
    name := "clone"
    self_ty := Ty.named "Self"
    params := []
    ret := Ty.named "Self"
  }]
  assoc_types := []
  parent_traits := []
}

def DebugTrait : TraitDef := {
  name := "Debug"
  type_params := []
  methods := [{
    name := "debug"
    self_ty := Ty.named "Self"
    params := []
    ret := Ty.named "String"
  }]
  assoc_types := []
  parent_traits := []
}

def UserType : Ty := Ty.named "User"

def CloneImpl : TraitImpl := {
  trait_name := "Clone"
  for_type := UserType
  type_params := []
  assoc_type_bindings := []
  method_impls := []
  where_clause := []
}

def DebugImpl : TraitImpl := {
  trait_name := "Debug"
  for_type := UserType
  type_params := []
  assoc_type_bindings := []
  method_impls := []
  where_clause := []
}

def multiTraitConstraint : BindConstraint := {
  dispatch := DispatchMode.static
  trait_bounds := ["Clone", "Debug"]
  sized := true
}

def testMultiTraitBounds : Bool :=
  let env : BindEnv := {
    trait_env := [("Clone", CloneTrait), ("Debug", DebugTrait)]
    impl_registry := [CloneImpl, DebugImpl]
    vtable_registry := []
    monomorphized := []
  }
  satisfiesBindConstraint env UserType multiTraitConstraint

#eval testMultiTraitBounds  -- Expected: true

-- Example 7: Monomorphization
def genericProcessFn : FnDefBind :=
  let T := TyVar.mk 0
  {
    name := "process"
    type_params := [{
      var := T
      bind_constraint := some {
        dispatch := DispatchMode.static
        trait_bounds := ["Clone"]
        sized := true
      }
    }]
    params := [("item", Ty.var T)]
    bind_params := []
    ret := Ty.int
    body := ()
  }

def testMonomorphization : Bool :=
  match monomorphizeFunction genericProcessFn [UserType] with
  | some mono =>
      mono.original_name == "process" &&
      mono.instantiated_for == UserType &&
      mono.dispatch_mode == DispatchMode.static &&
      mono.fn_def.type_params.isEmpty
  | none => false

#eval testMonomorphization  -- Expected: true

-- Example 8: Vtable lookup
def testVtableLookup : Bool :=
  let vtable : Vtable := {
    trait_name := "Drawable"
    for_type := CircleType
    entries := [{
      method_name := "draw"
      method_signature := ([], Ty.int)
    }]
  }
  let registry := [vtable]
  match lookupVtable registry "Drawable" CircleType with
  | some v => v.trait_name == "Drawable"
  | none => false

#eval testVtableLookup  -- Expected: true

-- Example 9: Static dispatch no heap allocation
def testStaticNoHeap : Bool :=
  let mono : MonomorphizedFn := {
    original_name := "compute"
    instantiated_for := Ty.int
    fn_def := {
      name := "compute"
      type_params := []
      params := []
      bind_params := []
      ret := Ty.int
      body := ()
    }
    dispatch_mode := DispatchMode.static
  }
  staticDispatchNoHeap mono

#eval testStaticNoHeap  -- Expected: true

-- Example 10: Static dispatch is inlinable
def testStaticInlinable : Bool :=
  let mono : MonomorphizedFn := {
    original_name := "add"
    instantiated_for := Ty.int
    fn_def := {
      name := "add"
      type_params := []
      params := [("a", Ty.int), ("b", Ty.int)]
      bind_params := []
      ret := Ty.int
      body := ()
    }
    dispatch_mode := DispatchMode.static
  }
  staticDispatchInlinable mono

#eval testStaticInlinable  -- Expected: true

-- Example 11: Dispatch modes are exclusive
def testDispatchExclusive : Bool :=
  let staticParam : BindParam := {
    name := "x"
    bind_constraint := {
      dispatch := DispatchMode.static
      trait_bounds := []
      sized := true
    }
  }
  let dynamicParam : BindParam := {
    name := "y"
    bind_constraint := {
      dispatch := DispatchMode.dynamic
      trait_bounds := []
      sized := false
    }
  }
  usesStaticDispatch staticParam && !usesDynamicDispatch staticParam &&
  usesDynamicDispatch dynamicParam && !usesStaticDispatch dynamicParam

#eval testDispatchExclusive  -- Expected: true

-- Example 12: Complete bind call validation
def testBindCallValidation : Bool :=
  let env : BindEnv := {
    trait_env := [("Drawable", DrawableTrait)]
    impl_registry := [DrawableImpl]
    vtable_registry := []
    monomorphized := []
  }
  let fn : FnDefBind := {
    name := "render"
    type_params := []
    params := []
    bind_params := [staticDrawableParam]
    ret := Ty.int
    body := ()
  }
  checkBindCall env fn staticDrawableParam CircleType

#eval testBindCallValidation  -- Expected: true

-- Example 13: Unique monomorphization check
def testUniqueMonomorphization : Bool :=
  let mono1 : MonomorphizedFn := {
    original_name := "process"
    instantiated_for := UserType
    fn_def := genericProcessFn
    dispatch_mode := DispatchMode.static
  }
  let mono2 : MonomorphizedFn := {
    original_name := "process"
    instantiated_for := CircleType
    fn_def := genericProcessFn
    dispatch_mode := DispatchMode.static
  }
  let fns := [mono1, mono2]
  uniqueMonomorphization fns "process" UserType &&
  uniqueMonomorphization fns "process" CircleType

#eval testUniqueMonomorphization  -- Expected: true

-- Example 14: Static requires Sized
def testStaticRequiresSized : Bool :=
  staticRequiresSized staticDrawableConstraint

#eval testStaticRequiresSized  -- Expected: true

-- Example 15: Dynamic doesn't require Sized
def testDynamicNoSizedRequired : Bool :=
  !staticRequiresSized dynamicDrawableConstraint

#eval testDynamicNoSizedRequired  -- Expected: true

-- Summary: All test cases verify key static polymorphism properties
-- 1. Static dispatch with trait bounds
-- 2. Dynamic dispatch (default)
-- 3. Sized constraint for static dispatch
-- 4. Vtable generation and lookup
-- 5. Monomorphization
-- 6. Performance guarantees (no heap, inlinable)
-- 7. Dispatch mode exclusivity
-- 8. Complete validation
-- 9. Uniqueness
-- 10. Default behavior
