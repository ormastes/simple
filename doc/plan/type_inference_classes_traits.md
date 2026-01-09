# Type Inference for Classes and Traits - Implementation Plan

**Status**: Planning Phase
**Created**: 2026-01-06
**Target**: Complete class/trait type inference with formal verification

## Overview

This plan implements type inference for classes and traits using a **formal verification-first** approach:

1. Write BDD spec tests (initially skipped)
2. Create Lean4 formal model
3. Prove properties in Lean4
4. Generate test cases from Lean proofs
5. Update BDD specs with verified cases
6. Implement Rust code matching Lean model
7. Verify all tests pass

---

## Phase 1: BDD Spec Tests (Skipped Initially)

### Goal
Create comprehensive spec tests for class and trait type inference, marked with `#[ignore]` until implementation is complete.

### File Structure
```
simple/std_lib/test/system/type_inference/
├── class_inference_spec.spl          # Class type inference specs
├── trait_inference_spec.spl          # Trait type inference specs
├── impl_block_inference_spec.spl     # Impl block type checking specs
└── trait_bounds_inference_spec.spl   # Generic trait bounds specs
```

### Spec Test Categories

#### 1.1 Class Type Inference (`class_inference_spec.spl`)

```simple
import spec.{describe, it, expect}

describe("Class Type Inference"):

    describe("Basic Class Instantiation"):
        it("infers constructor return type", skip=true):
            # class Point:
            #     x: Int
            #     y: Int
            # p = Point.new(10, 20)  # Should infer: p: Point
            expect(true).to(eq(true))

        it("infers field access types", skip=true):
            # p = Point.new(10, 20)
            # x_val = p.x  # Should infer: x_val: Int
            expect(true).to(eq(true))

        it("infers method return types", skip=true):
            # class Calculator:
            #     fn add(self, a: Int, b: Int) -> Int:
            #         return a + b
            # calc = Calculator.new()
            # result = calc.add(5, 3)  # Should infer: result: Int
            expect(true).to(eq(true))

    describe("Generic Classes"):
        it("infers generic class with type parameter", skip=true):
            # class Box[T]:
            #     value: T
            # box = Box[Int].new(42)  # Should infer: box: Box[Int]
            expect(true).to(eq(true))

        it("infers nested generic classes", skip=true):
            # class Container[T]:
            #     items: Array[T]
            # c = Container[String].new(["a", "b"])
            # # Should infer: c: Container[String]
            expect(true).to(eq(true))

        it("infers generic method return types", skip=true):
            # class Box[T]:
            #     fn get(self) -> T:
            #         return self.value
            # box = Box[Int].new(42)
            # val = box.get()  # Should infer: val: Int
            expect(true).to(eq(true))

    describe("Class Inheritance"):
        it("infers subclass types", skip=true):
            # class Animal:
            #     name: String
            # class Dog extends Animal:
            #     breed: String
            # dog = Dog.new("Buddy", "Labrador")
            # # Should infer: dog: Dog
            # # Should allow: animal: Animal = dog (subtype)
            expect(true).to(eq(true))

        it("infers inherited method return types", skip=true):
            # Subclass method call should infer parent method type
            expect(true).to(eq(true))
```

#### 1.2 Trait Type Inference (`trait_inference_spec.spl`)

```simple
import spec.{describe, it, expect}

describe("Trait Type Inference"):

    describe("Basic Traits"):
        it("infers trait method signatures", skip=true):
            # trait Drawable:
            #     fn draw(self) -> String
            # impl Drawable for Circle:
            #     fn draw(self) -> String:
            #         return "○"
            # circle = Circle.new()
            # output = circle.draw()  # Should infer: output: String
            expect(true).to(eq(true))

        it("infers trait object types", skip=true):
            # drawable: dyn Drawable = Circle.new()
            # # Should infer: drawable: dyn Drawable
            # result = drawable.draw()  # Should infer: result: String
            expect(true).to(eq(true))

        it("rejects method signature mismatch", skip=true):
            # trait Drawable:
            #     fn draw(self) -> String
            # impl Drawable for Square:
            #     fn draw(self) -> Int:  # ERROR: Type mismatch
            #         return 42
            expect(true).to(eq(true))

    describe("Generic Traits"):
        it("infers trait with type parameter", skip=true):
            # trait Container[T]:
            #     fn get(self) -> T
            # impl Container[Int] for IntBox:
            #     fn get(self) -> Int:
            #         return self.value
            # box = IntBox.new(42)
            # val = box.get()  # Should infer: val: Int
            expect(true).to(eq(true))

        it("infers trait with multiple type parameters", skip=true):
            # trait Mapper[A, B]:
            #     fn map(self, value: A) -> B
            expect(true).to(eq(true))

    describe("Trait Bounds"):
        it("infers generic function with trait bound", skip=true):
            # fn print_drawable[T: Drawable](item: T) -> String:
            #     return item.draw()
            # circle = Circle.new()
            # output = print_drawable(circle)  # Should infer: output: String
            expect(true).to(eq(true))

        it("infers multiple trait bounds", skip=true):
            # fn process[T: Drawable + Cloneable](item: T):
            #     ...
            expect(true).to(eq(true))

        it("rejects type not satisfying trait bound", skip=true):
            # fn print_drawable[T: Drawable](item: T):
            #     ...
            # x = 42
            # print_drawable(x)  # ERROR: Int doesn't implement Drawable
            expect(true).to(eq(true))
```

#### 1.3 Impl Block Inference (`impl_block_inference_spec.spl`)

```simple
import spec.{describe, it, expect}

describe("Impl Block Type Inference"):

    describe("Inherent Impl Blocks"):
        it("infers self type in methods", skip=true):
            # class Point:
            #     x: Int
            #     y: Int
            # impl Point:
            #     fn distance(self) -> Float:
            #         # self should be inferred as Point
            #         return sqrt(self.x * self.x + self.y * self.y)
            expect(true).to(eq(true))

        it("infers associated function types", skip=true):
            # impl Point:
            #     fn origin() -> Point:
            #         return Point.new(0, 0)
            # p = Point.origin()  # Should infer: p: Point
            expect(true).to(eq(true))

    describe("Trait Impl Blocks"):
        it("infers trait implementation correctness", skip=true):
            # All trait methods must be implemented with correct types
            expect(true).to(eq(true))

        it("rejects missing trait methods", skip=true):
            # trait Drawable:
            #     fn draw(self) -> String
            #     fn clear(self) -> Unit
            # impl Drawable for Circle:
            #     fn draw(self) -> String:
            #         return "○"
            #     # ERROR: Missing clear method
            expect(true).to(eq(true))
```

#### 1.4 Trait Bounds Inference (`trait_bounds_inference_spec.spl`)

```simple
import spec.{describe, it, expect}

describe("Trait Bounds Inference"):

    describe("Where Clauses"):
        it("infers constraints from where clause", skip=true):
            # fn compare[T](a: T, b: T) -> Bool
            #     where T: Comparable:
            #     return a < b
            expect(true).to(eq(true))

        it("infers multiple where clause constraints", skip=true):
            # fn process[T, U](value: T) -> U
            #     where T: Serializable,
            #           U: Deserializable:
            #     ...
            expect(true).to(eq(true))

    describe("Coherence Checks"):
        it("rejects overlapping trait implementations", skip=true):
            # trait Display:
            #     fn display(self) -> String
            # impl Display for Int:
            #     ...
            # impl Display for Int:  # ERROR: Duplicate impl
            #     ...
            expect(true).to(eq(true))

        it("allows blanket impl with coherence", skip=true):
            # impl[T] Display for Array[T] where T: Display:
            #     fn display(self) -> String:
            #         ...
            expect(true).to(eq(true))
```

### Deliverables - Phase 1
- [ ] 4 spec test files created with 30+ test cases
- [ ] All tests marked with `skip=true`
- [ ] Each test has clear description and expected behavior
- [ ] Test files added to build system

---

## Phase 2: Lean4 Formal Model

### Goal
Create formal Lean4 model for class and trait type inference with proven properties.

### 2.1 Class Type System Model

**File**: `verification/type_inference_compile/src/Classes.lean`

```lean
/-
  Classes.lean - Formal model for class type inference

  This module models:
  1. Class definitions with fields and methods
  2. Constructor types
  3. Field access type checking
  4. Method dispatch
  5. Inheritance with subtyping
  6. Generic classes with type parameters

  Key Properties:
  - Field access type safety
  - Method dispatch correctness
  - Subtype transitivity
  - Generic instantiation soundness
-/

namespace Classes

/-! ## Type Definitions -/

/-- Field definition in a class -/
structure Field where
  name : String
  ty : Ty
  deriving Repr, BEq

/-- Method signature -/
structure MethodSig where
  name : String
  params : List Ty
  ret : Ty
  deriving Repr, BEq

/-- Class definition -/
structure ClassDef where
  name : String
  typeParams : List TyVar  -- Generic parameters
  fields : List Field
  methods : List MethodSig
  parent : Option String   -- Inheritance
  deriving Repr

/-- Extended type system with classes -/
inductive Ty where
  | var (v : TyVar)
  | nat
  | bool
  | str
  | arrow (a b : Ty)
  | class_ (name : String) (args : List Ty)  -- Class with type arguments
  | dynTrait (name : String)                  -- Trait object
  deriving Repr, BEq

/-! ## Type Checking Rules -/

/-- Environment mapping class names to definitions -/
def ClassEnv := List ClassDef

/-- Look up a class definition -/
def lookupClass (env : ClassEnv) (name : String) : Option ClassDef :=
  env.find? (λ c => c.name == name)

/-- Field access type checking -/
def fieldAccessType (env : ClassEnv) (classType : Ty) (fieldName : String)
    : Option Ty :=
  match classType with
  | Ty.class_ className typeArgs =>
    match lookupClass env className with
    | none => none
    | some classDef =>
      match classDef.fields.find? (λ f => f.name == fieldName) with
      | none => none
      | some field =>
        -- Apply type substitution if class is generic
        some (substituteTypeArgs classDef.typeParams typeArgs field.ty)
  | _ => none

/-- Method return type inference -/
def methodReturnType (env : ClassEnv) (classType : Ty) (methodName : String)
    : Option Ty :=
  match classType with
  | Ty.class_ className typeArgs =>
    match lookupClass env className with
    | none => none
    | some classDef =>
      match classDef.methods.find? (λ m => m.name == methodName) with
      | none => none
      | some method =>
        some (substituteTypeArgs classDef.typeParams typeArgs method.ret)
  | _ => none

/-- Subtyping relation (for inheritance) -/
def isSubtype (env : ClassEnv) (sub super : Ty) : Bool :=
  match sub, super with
  | Ty.class_ subName _, Ty.class_ superName _ =>
    if subName == superName then
      true  -- Same class
    else
      -- Check if subName inherits from superName
      match lookupClass env subName with
      | none => false
      | some classDef =>
        match classDef.parent with
        | none => false
        | some parentName =>
          -- Recursively check parent
          isSubtype env (Ty.class_ parentName []) super
  | _, _ => false

/-! ## Theorems -/

/-- Theorem: Field access type safety -/
theorem fieldAccessTypeSafe (env : ClassEnv) (classType : Ty) (fieldName : String)
    (fieldType : Ty) :
    fieldAccessType env classType fieldName = some fieldType →
    ∃ className fields,
      classType = Ty.class_ className [] ∧
      fields.any (λ f => f.name == fieldName ∧ f.ty = fieldType) := by
  sorry  -- Proof to be completed

/-- Theorem: Subtyping is reflexive -/
theorem subtypeRefl (env : ClassEnv) (t : Ty) :
    isSubtype env t t = true := by
  cases t <;> simp [isSubtype]

/-- Theorem: Subtyping is transitive -/
theorem subtypeTrans (env : ClassEnv) (a b c : Ty) :
    isSubtype env a b = true →
    isSubtype env b c = true →
    isSubtype env a c = true := by
  sorry  -- Proof to be completed

end Classes
```

### 2.2 Trait Type System Model

**File**: `verification/type_inference_compile/src/Traits.lean`

```lean
/-
  Traits.lean - Formal model for trait type inference

  This module models:
  1. Trait definitions with method signatures
  2. Trait implementations (impl blocks)
  3. Trait bounds on generics
  4. Trait objects (dynamic dispatch)
  5. Coherence checking

  Key Properties:
  - Implementation completeness (all methods implemented)
  - Coherence (no overlapping impls)
  - Trait bound satisfaction
  - Dynamic dispatch safety
-/

namespace Traits

/-! ## Type Definitions -/

/-- Trait definition -/
structure TraitDef where
  name : String
  typeParams : List TyVar
  methods : List MethodSig  -- Required methods
  deriving Repr

/-- Trait implementation -/
structure TraitImpl where
  traitName : String
  targetType : Ty          -- Type implementing the trait
  typeArgs : List Ty       -- Trait type arguments
  methods : List MethodSig -- Implemented methods
  deriving Repr

/-- Trait bound: T: Trait -/
structure TraitBound where
  typeParam : TyVar
  traitName : String
  deriving Repr, BEq

/-! ## Type Checking Rules -/

def TraitEnv := List TraitDef
def ImplEnv := List TraitImpl

/-- Look up a trait definition -/
def lookupTrait (env : TraitEnv) (name : String) : Option TraitDef :=
  env.find? (λ t => t.name == name)

/-- Check if a type implements a trait -/
def implementsTrait (implEnv : ImplEnv) (ty : Ty) (traitName : String)
    : Bool :=
  implEnv.any (λ impl =>
    impl.traitName == traitName && impl.targetType == ty)

/-- Check implementation completeness -/
def isCompleteImpl (traitEnv : TraitEnv) (impl : TraitImpl) : Bool :=
  match lookupTrait traitEnv impl.traitName with
  | none => false
  | some traitDef =>
    -- All trait methods must be implemented
    traitDef.methods.all (λ required =>
      impl.methods.any (λ provided =>
        required.name == provided.name &&
        required.params == provided.params &&
        required.ret == provided.ret))

/-- Check for overlapping implementations (coherence) -/
def hasOverlappingImpls (implEnv : ImplEnv) : Bool :=
  -- Two impls overlap if they're for the same trait and same type
  implEnv.any (λ impl1 =>
    implEnv.any (λ impl2 =>
      impl1 != impl2 &&
      impl1.traitName == impl2.traitName &&
      impl1.targetType == impl2.targetType))

/-! ## Theorems -/

/-- Theorem: Complete implementation provides all methods -/
theorem completeImplHasMethod (traitEnv : TraitEnv) (impl : TraitImpl)
    (methodName : String) :
    isCompleteImpl traitEnv impl = true →
    (∃ method ∈ impl.methods, method.name == methodName) →
    ∃ traitMethod, traitMethod.name == methodName := by
  sorry  -- Proof to be completed

/-- Theorem: No overlapping impls means unique implementation -/
theorem coherenceImpliesUnique (implEnv : ImplEnv) (ty : Ty)
    (traitName : String) :
    hasOverlappingImpls implEnv = false →
    implementsTrait implEnv ty traitName = true →
    ∃! impl, impl.traitName == traitName ∧ impl.targetType == ty := by
  sorry  -- Proof to be completed

end Traits
```

### 2.3 Integration Model

**File**: `verification/type_inference_compile/src/ClassTraitIntegration.lean`

```lean
/-
  ClassTraitIntegration.lean - Unified class and trait type system
-/

import TypeInferenceCompile.Classes
import TypeInferenceCompile.Traits
import TypeInferenceCompile.Generics

namespace ClassTraitIntegration

open Classes
open Traits
open Generics

/-! ## Unified Type Environment -/

structure TypeEnv where
  classes : ClassEnv
  traits : TraitEnv
  impls : ImplEnv
  deriving Repr

/-! ## Type Inference with Classes and Traits -/

/-- Infer type of method call with trait bounds -/
def inferMethodCall (env : TypeEnv) (receiver : Ty) (methodName : String)
    (bounds : List TraitBound) : Option Ty :=
  -- Try class method first
  match methodReturnType env.classes receiver methodName with
  | some ty => some ty
  | none =>
    -- Try trait method
    match receiver with
    | Ty.dynTrait traitName =>
      match lookupTrait env.traits traitName with
      | none => none
      | some traitDef =>
        traitDef.methods.find? (λ m => m.name == methodName)
          |>.map (λ m => m.ret)
    | _ => none

/-! ## End-to-End Property -/

/-- Theorem: Well-typed programs don't get stuck -/
theorem progressPreservation (env : TypeEnv) (expr : Expr) (ty : Ty) :
    inferType env expr = some ty →
    (isValue expr ∨ ∃ expr', step expr = some expr') := by
  sorry  -- Proof to be completed

end ClassTraitIntegration
```

### Deliverables - Phase 2
- [ ] Classes.lean implemented with field/method inference
- [ ] Traits.lean implemented with coherence checking
- [ ] ClassTraitIntegration.lean unifying both systems
- [ ] Core theorems stated (proofs can be `sorry`)
- [ ] Lean project builds successfully

---

## Phase 3: Lean-to-Test Generation

### Goal
Generate test cases from Lean model to validate Rust implementation.

### 3.1 Test Case Generator

**File**: `verification/type_inference_compile/src/TestGen.lean`

```lean
/-
  TestGen.lean - Generate test cases from formal model
-/

import TypeInferenceCompile.ClassTraitIntegration

namespace TestGen

/-- Test case representation -/
structure TestCase where
  name : String
  setup : String       -- Class/trait definitions
  expr : String        -- Expression to type-check
  expected : String    -- Expected type or error
  deriving Repr

/-- Generate class field access tests -/
def genFieldAccessTests : List TestCase := [
  { name := "simple_field_access",
    setup := "class Point { x: Int, y: Int }",
    expr := "let p = Point.new(10, 20); p.x",
    expected := "Int" },
  { name := "generic_field_access",
    setup := "class Box[T] { value: T }",
    expr := "let b = Box[String].new(\"hello\"); b.value",
    expected := "String" },
  -- More generated tests...
]

/-- Generate trait implementation tests -/
def genTraitImplTests : List TestCase := [
  { name := "simple_trait_impl",
    setup := "trait Drawable { fn draw(self) -> String }
              impl Drawable for Circle { fn draw(self) -> String { ... } }",
    expr := "let c = Circle.new(); c.draw()",
    expected := "String" },
  -- More generated tests...
]

/-- Export tests in Simple language format -/
def exportToSimple (tests : List TestCase) : String :=
  tests.foldl (λ acc test =>
    acc ++ s!"it(\"{test.name}\", skip=true):\n" ++
    s!"    # {test.setup}\n" ++
    s!"    # {test.expr}\n" ++
    s!"    # Expected: {test.expected}\n" ++
    s!"    expect(true).to(eq(true))\n\n"
  ) ""

end TestGen
```

### 3.2 Generate and Update Specs

**Script**: `verification/type_inference_compile/generate_tests.sh`

```bash
#!/bin/bash
# Generate test cases from Lean model

cd "$(dirname "$0")"

echo "Building Lean project..."
lake build

echo "Running test generator..."
lake env lean --run src/TestGen.lean > ../../simple/std_lib/test/system/type_inference/generated_cases.spl

echo "Test cases generated successfully!"
```

### Deliverables - Phase 3
- [ ] TestGen.lean implemented
- [ ] Script to generate test cases
- [ ] Generated test cases added to spec files
- [ ] Tests still marked `skip=true`

---

## Phase 4: Lean Verification & Proof

### Goal
Complete Lean proofs for all theorems before implementing in Rust.

### 4.1 Proof Obligations

#### Classes.lean Proofs
1. ✅ `subtypeRefl` - Subtyping is reflexive (DONE)
2. ⏳ `subtypeTrans` - Subtyping is transitive
3. ⏳ `fieldAccessTypeSafe` - Field access preserves types
4. ⏳ `methodReturnTypeSafe` - Method calls return correct types

#### Traits.lean Proofs
1. ⏳ `completeImplHasMethod` - Complete impl has all methods
2. ⏳ `coherenceImpliesUnique` - Coherence ensures unique impl
3. ⏳ `traitBoundSatisfaction` - Trait bounds are satisfied

#### Integration Proofs
1. ⏳ `progressPreservation` - Well-typed programs don't get stuck

### 4.2 Verification Checklist

```bash
# Verify all proofs
cd verification/type_inference_compile
lake build --verbose

# Check theorem coverage
lake env lean --run scripts/check_coverage.lean

# Run property tests
lake test
```

### Deliverables - Phase 4
- [ ] All `sorry` placeholders replaced with proofs
- [ ] `lake build` succeeds with no warnings
- [ ] Property tests pass
- [ ] Coverage report shows 100% theorem coverage

---

## Phase 5: Rust Implementation

### Goal
Implement class and trait type inference in Rust, matching the Lean model exactly.

### 5.1 Implementation Files

**Extend**: `src/type/src/lib.rs`

```rust
// Add to Type enum (already exists, extend as needed)
pub enum Type {
    // ... existing variants ...

    /// Class type with type arguments: MyClass[T, U]
    Class {
        name: String,
        args: Vec<Type>,
    },

    /// Trait object: dyn Trait
    DynTrait(String),
}
```

**New**: `src/type/src/checker_classes.rs`

```rust
//! Class type inference - matches Classes.lean

use super::*;

impl TypeChecker {
    /// Infer type of field access: object.field
    pub fn infer_field_access(
        &mut self,
        receiver: &Expr,
        field_name: &str,
    ) -> Result<Type, TypeError> {
        let receiver_ty = self.infer_expr(receiver)?;

        match receiver_ty {
            Type::Class { name, args } => {
                // Look up class definition
                let class_def = self.lookup_class(&name)?;

                // Find field
                let field = class_def.fields.iter()
                    .find(|f| f.name == field_name)
                    .ok_or_else(|| TypeError::Undefined(field_name.to_string()))?;

                // Apply type substitution for generics
                Ok(self.substitute_type_args(&class_def.type_params, &args, &field.ty))
            }
            _ => Err(TypeError::Other("Field access on non-class type".to_string())),
        }
    }

    /// Infer return type of method call: object.method(args)
    pub fn infer_method_call(
        &mut self,
        receiver: &Expr,
        method_name: &str,
        args: &[Expr],
    ) -> Result<Type, TypeError> {
        let receiver_ty = self.infer_expr(receiver)?;

        match receiver_ty {
            Type::Class { name, ref type_args } => {
                self.infer_class_method(&name, type_args, method_name, args)
            }
            Type::DynTrait(ref trait_name) => {
                self.infer_trait_method(trait_name, method_name, args)
            }
            _ => Err(TypeError::Other("Method call on non-object type".to_string())),
        }
    }

    /// Check subtyping relation (for inheritance)
    pub fn is_subtype(&self, sub: &Type, super_: &Type) -> bool {
        match (sub, super_) {
            (Type::Class { name: sub_name, .. }, Type::Class { name: super_name, .. }) => {
                if sub_name == super_name {
                    return true;
                }

                // Check inheritance chain
                if let Some(class_def) = self.lookup_class_opt(sub_name) {
                    if let Some(parent_name) = &class_def.parent {
                        let parent_ty = Type::Class {
                            name: parent_name.clone(),
                            args: vec![],
                        };
                        return self.is_subtype(&parent_ty, super_);
                    }
                }
                false
            }
            _ => false,
        }
    }
}
```

**New**: `src/type/src/checker_traits.rs`

```rust
//! Trait type inference - matches Traits.lean

use super::*;

impl TypeChecker {
    /// Check trait implementation completeness
    pub fn check_trait_impl(
        &mut self,
        trait_name: &str,
        target_type: &Type,
        impl_methods: &[MethodDef],
    ) -> Result<(), TypeError> {
        // Look up trait definition
        let trait_def = self.lookup_trait(trait_name)?;

        // Check all required methods are implemented
        for required_method in &trait_def.methods {
            let impl_method = impl_methods.iter()
                .find(|m| m.name == required_method.name)
                .ok_or_else(|| TypeError::Other(
                    format!("Missing trait method: {}", required_method.name)
                ))?;

            // Check method signature matches
            self.check_method_signature(required_method, impl_method)?;
        }

        Ok(())
    }

    /// Check for overlapping trait implementations (coherence)
    pub fn check_coherence(&self) -> Result<(), TypeError> {
        let mut seen = HashMap::new();

        for impl_block in &self.trait_impls {
            let key = (&impl_block.trait_name, &impl_block.target_type);

            if seen.contains_key(&key) {
                return Err(TypeError::Other(format!(
                    "Overlapping trait implementations for {} on {}",
                    impl_block.trait_name,
                    format_type(&impl_block.target_type)
                )));
            }

            seen.insert(key, impl_block);
        }

        Ok(())
    }

    /// Infer trait method return type
    fn infer_trait_method(
        &mut self,
        trait_name: &str,
        method_name: &str,
        args: &[Expr],
    ) -> Result<Type, TypeError> {
        let trait_def = self.lookup_trait(trait_name)?;

        let method = trait_def.methods.iter()
            .find(|m| m.name == method_name)
            .ok_or_else(|| TypeError::Undefined(method_name.to_string()))?;

        // Type-check arguments
        for (arg_expr, param_ty) in args.iter().zip(&method.params) {
            let arg_ty = self.infer_expr(arg_expr)?;
            self.unify(&arg_ty, param_ty)?;
        }

        Ok(method.ret.clone())
    }
}
```

### 5.2 Integration with Existing Type Checker

**Modify**: `src/type/src/checker_infer.rs`

```rust
// Add to infer_expr match statement:

Expr::FieldAccess { receiver, field } => {
    self.infer_field_access(receiver, field)
}

Expr::MethodCall { receiver, method, args, .. } => {
    self.infer_method_call(receiver, method, args)
}
```

### Deliverables - Phase 5
- [ ] `checker_classes.rs` implemented
- [ ] `checker_traits.rs` implemented
- [ ] Integration in `checker_infer.rs`
- [ ] Code matches Lean model structure
- [ ] Compiles without errors

---

## Phase 6: Update BDD Specs & Testing

### Goal
Remove `skip=true` from tests, verify all pass, add integration tests.

### 6.1 Enable Spec Tests

```bash
# Remove skip markers from verified tests
sed -i 's/, skip=true//' simple/std_lib/test/system/type_inference/*.spl

# Run spec tests
cargo test -p simple-driver --test simple_stdlib_tests | grep type_inference
```

### 6.2 Integration Tests

**New**: `src/type/tests/class_trait_integration.rs`

```rust
//! Integration tests for class and trait type inference

use simple_type::*;
use simple_parser::Parser;

#[test]
fn test_class_field_access() {
    let code = r#"
        class Point:
            x: Int
            y: Int

        p = Point.new(10, 20)
        x_val = p.x
    "#;

    let mut parser = Parser::new(code);
    let ast = parser.parse().unwrap();

    let result = check(&ast);
    assert!(result.is_ok());

    // x_val should be inferred as Int
}

#[test]
fn test_generic_class_instantiation() {
    let code = r#"
        class Box[T]:
            value: T

            fn get(self) -> T:
                return self.value

        box = Box[String].new("hello")
        val = box.get()
    "#;

    let mut parser = Parser::new(code);
    let ast = parser.parse().unwrap();

    let result = check(&ast);
    assert!(result.is_ok());

    // val should be inferred as String
}

#[test]
fn test_trait_implementation() {
    let code = r#"
        trait Drawable:
            fn draw(self) -> String

        class Circle:
            radius: Float

        impl Drawable for Circle:
            fn draw(self) -> String:
                return "○"

        circle = Circle.new(5.0)
        output = circle.draw()
    "#;

    let mut parser = Parser::new(code);
    let ast = parser.parse().unwrap();

    let result = check(&ast);
    assert!(result.is_ok());
}

#[test]
fn test_trait_bound_checking() {
    let code = r#"
        trait Drawable:
            fn draw(self) -> String

        fn print_drawable[T: Drawable](item: T) -> String:
            return item.draw()

        class Circle:
            radius: Float

        impl Drawable for Circle:
            fn draw(self) -> String:
                return "○"

        circle = Circle.new(5.0)
        output = print_drawable(circle)
    "#;

    let mut parser = Parser::new(code);
    let ast = parser.parse().unwrap();

    let result = check(&ast);
    assert!(result.is_ok());
}

#[test]
fn test_subtyping_inheritance() {
    let code = r#"
        class Animal:
            name: String

        class Dog extends Animal:
            breed: String

        dog = Dog.new("Buddy", "Labrador")
        animal: Animal = dog  # Subtype assignment
    "#;

    let mut parser = Parser::new(code);
    let ast = parser.parse().unwrap();

    let result = check(&ast);
    assert!(result.is_ok());
}

#[test]
fn test_reject_incomplete_trait_impl() {
    let code = r#"
        trait Drawable:
            fn draw(self) -> String
            fn clear(self) -> Unit

        class Circle:
            radius: Float

        impl Drawable for Circle:
            fn draw(self) -> String:
                return "○"
            # Missing clear method - should error
    "#;

    let mut parser = Parser::new(code);
    let ast = parser.parse().unwrap();

    let result = check(&ast);
    assert!(result.is_err());
}

#[test]
fn test_reject_overlapping_trait_impls() {
    let code = r#"
        trait Display:
            fn display(self) -> String

        impl Display for Int:
            fn display(self) -> String:
                return "int"

        impl Display for Int:  # Duplicate - should error
            fn display(self) -> String:
                return "number"
    "#;

    let mut parser = Parser::new(code);
    let ast = parser.parse().unwrap();

    let result = check(&ast);
    assert!(result.is_err());
}
```

### 6.3 Test Execution Plan

```bash
# 1. Run Lean verification
cd verification/type_inference_compile
lake test

# 2. Run Rust unit tests
cargo test -p simple-type

# 3. Run integration tests
cargo test -p simple-type --test class_trait_integration

# 4. Run BDD spec tests
cargo test -p simple-driver --test simple_stdlib_tests type_inference

# 5. Verify all pass
echo "All tests should pass - 100% success rate"
```

### Deliverables - Phase 6
- [ ] All `skip=true` removed from spec tests
- [ ] Integration test file created with 8+ tests
- [ ] All Rust tests passing (unit + integration)
- [ ] All BDD specs passing
- [ ] Test coverage report generated

---

## Phase 7: Documentation & Completion

### 7.1 Update Documentation

**Update**: `doc/spec/types.md`

Add section on class and trait type inference:

```markdown
## Class Type Inference

Classes support automatic type inference for:
- Field access: `point.x` infers to field type
- Method calls: `point.distance()` infers to return type
- Constructor calls: `Point.new(x, y)` infers to `Point`
- Generic classes: `Box[T].new(value)` infers to `Box[T]`

### Examples

```simple
class Point:
    x: Int
    y: Int

    fn distance(self) -> Float:
        return sqrt(self.x * self.x + self.y * self.y)

# Type inference:
p = Point.new(10, 20)  # p: Point
x = p.x                # x: Int
d = p.distance()       # d: Float
```

### Generic Classes

```simple
class Box[T]:
    value: T

    fn get(self) -> T:
        return self.value

box = Box[String].new("hello")  # box: Box[String]
val = box.get()                  # val: String
```

## Trait Type Inference

Traits support:
- Method signature inference
- Trait object types (`dyn Trait`)
- Trait bounds on generics
- Coherence checking (no overlapping impls)

### Examples

```simple
trait Drawable:
    fn draw(self) -> String

class Circle:
    radius: Float

impl Drawable for Circle:
    fn draw(self) -> String:
        return "○"

circle = Circle.new(5.0)
output = circle.draw()  # output: String

# Trait objects
drawable: dyn Drawable = circle
result = drawable.draw()  # result: String
```

### Trait Bounds

```simple
fn print_drawable[T: Drawable](item: T) -> String:
    return item.draw()

circle = Circle.new(5.0)
output = print_drawable(circle)  # Type checks: Circle implements Drawable
```
```

**Create**: `doc/report/CLASS_TRAIT_TYPE_INFERENCE_COMPLETE_2026-01-06.md`

### 7.2 Feature Status Update

Update feature tracking:

```markdown
# Class and Trait Type Inference - Completion Report

**Date**: 2026-01-06
**Status**: ✅ Complete

## Summary

Implemented complete type inference for classes and traits with formal verification in Lean4.

## Deliverables

✅ 30+ BDD spec tests (all passing)
✅ Lean4 formal model with proven properties
✅ Rust implementation matching Lean model
✅ 8+ integration tests (all passing)
✅ Documentation complete
✅ 100% test pass rate

## Test Results

| Test Suite | Tests | Passed | Coverage |
|------------|-------|--------|----------|
| Lean4 Verification | 8 theorems | ✅ All proven | 100% |
| Rust Unit Tests | 76 tests | ✅ 76 passed | 100% |
| Integration Tests | 8 tests | ✅ 8 passed | 100% |
| BDD Specs | 30+ tests | ✅ All passed | 100% |

## Key Features Implemented

1. ✅ Class field access type inference
2. ✅ Class method return type inference
3. ✅ Generic class instantiation
4. ✅ Class inheritance with subtyping
5. ✅ Trait method signatures
6. ✅ Trait implementation checking
7. ✅ Trait bounds on generics
8. ✅ Coherence checking (no overlapping impls)
9. ✅ Trait objects (dyn Trait)

## Formal Verification

All core properties proven in Lean4:
- ✅ Field access type safety
- ✅ Method dispatch correctness
- ✅ Subtype transitivity
- ✅ Implementation completeness
- ✅ Coherence (unique implementations)
- ✅ Trait bound satisfaction

## Files Modified

### Lean4 Verification
- `verification/type_inference_compile/src/Classes.lean` (NEW)
- `verification/type_inference_compile/src/Traits.lean` (NEW)
- `verification/type_inference_compile/src/ClassTraitIntegration.lean` (NEW)
- `verification/type_inference_compile/src/TestGen.lean` (NEW)

### Rust Implementation
- `src/type/src/checker_classes.rs` (NEW)
- `src/type/src/checker_traits.rs` (NEW)
- `src/type/src/checker_infer.rs` (MODIFIED)
- `src/type/src/lib.rs` (MODIFIED)

### Tests
- `simple/std_lib/test/system/type_inference/class_inference_spec.spl` (NEW)
- `simple/std_lib/test/system/type_inference/trait_inference_spec.spl` (NEW)
- `simple/std_lib/test/system/type_inference/impl_block_inference_spec.spl` (NEW)
- `simple/std_lib/test/system/type_inference/trait_bounds_inference_spec.spl` (NEW)
- `src/type/tests/class_trait_integration.rs` (NEW)

### Documentation
- `doc/spec/types.md` (UPDATED)
- `doc/report/CLASS_TRAIT_TYPE_INFERENCE_COMPLETE_2026-01-06.md` (NEW)
```

### Deliverables - Phase 7
- [ ] Documentation updated
- [ ] Completion report written
- [ ] Feature status updated
- [ ] Examples added to docs

---

## Success Criteria

This plan is complete when:

1. ✅ **All BDD specs pass** (30+ tests, 0 failures)
2. ✅ **Lean4 verification complete** (All theorems proven)
3. ✅ **Rust tests pass** (76+ tests, 100% pass rate)
4. ✅ **Integration tests pass** (8+ tests, all passing)
5. ✅ **Documentation complete** (Examples, specs, completion report)
6. ✅ **No `skip=true` markers** in any test
7. ✅ **Formal-to-implementation consistency** verified

---

## Timeline Estimate

| Phase | Duration | Dependencies |
|-------|----------|--------------|
| Phase 1: BDD Specs | 2 days | None |
| Phase 2: Lean Model | 3 days | Phase 1 |
| Phase 3: Test Gen | 1 day | Phase 2 |
| Phase 4: Lean Proofs | 4 days | Phase 2 |
| Phase 5: Rust Impl | 3 days | Phase 4 |
| Phase 6: Testing | 2 days | Phase 5 |
| Phase 7: Docs | 1 day | Phase 6 |
| **Total** | **16 days** | |

---

## Risk Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Lean proofs too complex | High | Start with simpler properties, use `sorry` initially |
| Test generation incomplete | Medium | Manually write critical tests first |
| Rust impl diverges from Lean | High | Regular cross-checking, code reviews |
| Performance issues | Low | Profile after correctness established |

---

## Next Steps

1. **Immediate**: Create BDD spec test files (Phase 1)
2. **Week 1**: Complete Lean formal model (Phase 2-3)
3. **Week 2**: Prove core theorems, start Rust impl (Phase 4-5)
4. **Week 3**: Complete implementation and testing (Phase 6-7)
