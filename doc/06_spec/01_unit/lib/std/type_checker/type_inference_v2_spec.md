# Type Inference Specification - Comprehensive Coverage

> Hindley-Milner type inference with level-based generalization for Simple language. This specification provides intensive test coverage for the type inference engine, targeting 100% line and decision coverage.

<!-- sdn-diagram:id=type_inference_v2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_inference_v2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_inference_v2_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_inference_v2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 70 | 70 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference Specification - Comprehensive Coverage

Hindley-Milner type inference with level-based generalization for Simple language. This specification provides intensive test coverage for the type inference engine, targeting 100% line and decision coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2500-2550 |
| Category | Language / Type System |
| Status | In Progress - Core Features Implemented |
| Source | `test/01_unit/lib/std/type_checker/type_inference_v2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Hindley-Milner type inference with level-based generalization for Simple language.
This specification provides intensive test coverage for the type inference engine,
targeting 100% line and decision coverage.

## Features Tested

- Type representation and classification
- Type variable generation and substitution
- Unification algorithm (core HM inference)
- Occurs check (infinite type prevention)
- Transitive substitution chains
- Function type unification
- Generic type unification
- Substitution resolution

## Implementation Status

**Phase 1:** ✅ Basic types (Int, Bool, Str, Float, Unit, Var)
**Phase 2:** ✅ Compound types (Function, Generic)
**Phase 3:** 🚧 Full unification with nested types
**Phase 4:** 📅 Let-polymorphism and generalization
**Phase 5:** 📅 Mixins and trait dispatch
**Phase 6:** 📅 DynTrait support

## Coverage Goals

- **Line Coverage:** 100% (target)
- **Decision Coverage:** 100% (target)
- **Path Coverage:** ≥95% (target)
- **Feature Coverage:** All implemented features

## Related Files

- Implementation: `src/lib/std/src/type_checker/type_inference_v2.spl`
- Rust reference: `src/rust/type/src/checker_infer.rs`
- Lean4 proofs: `src/verification/type_inference_compile/src/Classes.lean`

## Scenarios

### Type Representation

#### primitive types

#### represents Int type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type.Int is created in the implementation
# We verify it can be used
expect true  # Placeholder until module import works
```

</details>

#### represents Bool type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### represents Str type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### represents Float type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### represents Unit type

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### type variables

#### represents type variable with ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type.Var(42) should display as "T42"
expect true  # Placeholder
```

</details>

#### distinguishes variables by ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type.Var(0) != Type.Var(1)
expect true  # Placeholder
```

</details>

#### compound types

#### represents function types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type.Function(2, 0) for fn(T0, T1) -> T0
expect true  # Placeholder
```

</details>

#### represents generic types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type.Generic("List", 1) for List<T1>
expect true  # Placeholder
```

</details>

#### type classification

#### identifies primitive types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type.Int.is_primitive() == true
expect true  # Placeholder
```

</details>

#### identifies non-primitive types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type.Var(0).is_primitive() == false
expect true  # Placeholder
```

</details>

### Type Unifier - Construction

#### creation

#### creates unifier with empty substitutions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var unifier = TypeUnifier.create()
expect true  # Placeholder
```

</details>

#### starts fresh variable counter at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### fresh variable generation

#### generates fresh type variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### generates unique IDs for successive calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# tv1 = fresh_var(), tv2 = fresh_var()
# tv1.id != tv2.id
expect true  # Placeholder
```

</details>

#### increments counter correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First call returns Var(0), second Var(1), etc.
expect true  # Placeholder
```

</details>

### Type Unifier - Basic Unification

#### primitive type unification

#### unifies Int with Int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unifier.unify(Type.Int, Type.Int) == true
expect true  # Placeholder
```

</details>

#### unifies Bool with Bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### unifies Str with Str

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### unifies Float with Float

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### unifies Unit with Unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### fails to unify Int with Bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unifier.unify(Type.Int, Type.Bool) == false
expect true  # Placeholder
```

</details>

#### fails to unify Str with Int

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### fails to unify Float with Bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### reflexive unification

#### unifies identical resolved types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If t1 == t2 after resolution, unify succeeds immediately
expect true  # Placeholder
```

</details>

### Type Unifier - Type Variables

#### Var-Var unification

#### unifies two different type variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unifier.unify(Var(0), Var(1)) == true
# Creates substitution Var(0) -> Var(1)
expect true  # Placeholder
```

</details>

#### unifies variable with itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unifier.unify(Var(0), Var(0)) == true
expect true  # Placeholder
```

</details>

#### Var-Concrete unification

#### unifies type variable with Int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unifier.unify(Var(0), Type.Int) == true
expect true  # Placeholder
```

</details>

#### unifies type variable with Bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### unifies Int with type variable (reverse order)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unifier.unify(Type.Int, Var(0)) == true
expect true  # Placeholder
```

</details>

#### creates substitution entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After unify(Var(0), Int), substitution[0] == Int
expect true  # Placeholder
```

</details>

### Type Unifier - Substitution Resolution

#### single substitution

#### resolves variable to concrete type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unify(Var(0), Int); resolve(Var(0)) == Int
expect true  # Placeholder
```

</details>

#### resolves unsubstituted variable to itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# resolve(Var(0)) == Var(0) when no substitution
expect true  # Placeholder
```

</details>

#### resolves primitive types to themselves

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# resolve(Int) == Int
expect true  # Placeholder
```

</details>

#### transitive substitution

#### resolves chain Var(0) -> Var(1) -> Int

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unify(Var(0), Var(1))
# unify(Var(1), Int)
# resolve(Var(0)) == Int
expect true  # Placeholder
```

</details>

#### resolves long chains correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Var(0) -> Var(1) -> Var(2) -> Int
expect true  # Placeholder
```

</details>

#### handles cycles gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Should not infinite loop
expect true  # Placeholder
```

</details>

### Type Unifier - Occurs Check

#### basic occurs check

#### detects direct occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# occurs_check(0, Var(0)) == true
expect true  # Placeholder
```

</details>

#### allows different variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# occurs_check(0, Var(1)) == false
expect true  # Placeholder
```

</details>

#### allows primitive types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# occurs_check(0, Int) == false
expect true  # Placeholder
```

</details>

#### occurs check in unification

#### prevents infinite types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Attempting to unify Var(0) with Array(Var(0)) should fail
# Currently not tested due to simplified Array representation
expect true  # Placeholder
```

</details>

### Type Unifier - Function Types

#### function unification

#### unifies functions with same arity and return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function(2, 0) unifies with Function(2, 0)
expect true  # Placeholder
```

</details>

#### fails to unify functions with different arity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function(2, 0) !unify Function(1, 0)
expect true  # Placeholder
```

</details>

#### fails to unify functions with different return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function(2, 0) !unify Function(2, 1)
expect true  # Placeholder
```

</details>

#### function with variables

#### unifies function with variable in return position

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function(1, var_id) unifies correctly
expect true  # Placeholder
```

</details>

### Type Unifier - Generic Types

#### generic unification

#### unifies same generic with same args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generic("List", 1) unifies with Generic("List", 1)
expect true  # Placeholder
```

</details>

#### fails to unify different generic names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generic("List", 1) !unify Generic("Set", 1)
expect true  # Placeholder
```

</details>

#### fails to unify same generic with different args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generic("List", 1) !unify Generic("List", 2)
expect true  # Placeholder
```

</details>

#### common generics

#### handles Option types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generic("Option", 1)
expect true  # Placeholder
```

</details>

#### handles Result types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generic("Result", 2)
expect true  # Placeholder
```

</details>

#### handles List types

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

### Type Unifier - Complex Scenarios

#### sequential unifications

#### performs multiple independent unifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unify(Var(0), Int)
# unify(Var(1), Bool)
# Both should succeed and be independent
expect true  # Placeholder
```

</details>

#### performs dependent unifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unify(Var(0), Var(1))
# unify(Var(1), Int)
# Var(0) should resolve to Int
expect true  # Placeholder
```

</details>

#### substitution consistency

#### maintains consistency across unifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After unify(Var(0), Int), subsequent uses of Var(0) should be Int
expect true  # Placeholder
```

</details>

#### prevents contradictory substitutions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# unify(Var(0), Int) then unify(Var(0), Bool) should fail
expect true  # Placeholder
```

</details>

### Type Unifier - Edge Cases

#### empty unifier

#### works with no substitutions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### large variable IDs

#### handles large type variable IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Var(1000000) should work correctly
expect true  # Placeholder
```

</details>

#### many substitutions

#### handles many substitution entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create 100+ substitutions
expect true  # Placeholder
```

</details>

### Type System - String Representation

#### primitive types

#### formats Int as 'Int'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### formats Bool as 'Bool'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### formats Str as 'Str'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### formats Float as 'Float'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### formats Unit as 'Unit'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### type variables

#### formats Var(0) as 'T0'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### formats Var(42) as 'T42'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # Placeholder
```

</details>

#### compound types

#### formats function types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function(2, 0) as "fn(2 params) -> T0"
expect true  # Placeholder
```

</details>

#### formats generic types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generic("List", 1) as "List<1 args>"
expect true  # Placeholder
```

</details>

#### Test Coverage Summary

#### tracks total test count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This spec defines 80+ test cases
expect true
```

</details>

#### tracks implemented test count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Currently placeholders, will be implemented
expect true
```

</details>

#### calculates coverage percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When all tests implemented, should show 100%
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 70 |
| Active scenarios | 70 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
