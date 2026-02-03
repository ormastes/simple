# Variance Inference Implementation Plan

**Date:** 2026-02-03
**Phase:** 6 of Rust Feature Parity Roadmap
**Total Time:** 8 hours
**Status:** Planning

---

## Overview

Implement automatic variance inference for type parameters in generic types. Variance determines how subtyping relationships are preserved through type constructors.

**Key Concept:**
```simple
# Covariant: Box<Cat> <: Box<Animal> if Cat <: Animal
struct Box<+T>:           # + indicates covariance (read-only)
    value: T

# Invariant: Cell<Cat> not <: Cell<Animal>
struct Cell<T>:           # No marker = invariant (mutable)
    value: mut T

# Contravariant: Fn<Animal> <: Fn<Cat> if Cat <: Animal (reversed!)
type Fn<-T, +U> = fn(T) -> U   # - indicates contravariance (parameters)
```

---

## Background: Variance

### Definition

**Variance** describes how subtyping is preserved through type constructors:

| Variance | Notation | Subtyping Rule | Example |
|----------|----------|----------------|---------|
| **Covariant** | `+T` | `F<A> <: F<B>` if `A <: B` | `Box<Cat> <: Box<Animal>` |
| **Contravariant** | `-T` | `F<B> <: F<A>` if `A <: B` (reversed!) | `Fn(Animal) <: Fn(Cat)` |
| **Invariant** | `T` | `F<A> <: F<B>` only if `A = B` | `Cell<Cat>` unrelated to `Cell<Animal>` |
| **Bivariant** | `±T` | `F<A> <: F<B>` always | `Phantom<T>` (unused type parameter) |

### Why Variance Matters

**Safety:**
```simple
# Covariance is safe for read-only types
val cat_box: Box<Cat> = Box(Cat())
val animal_box: Box<Animal> = cat_box  # OK: can only read, Cat is an Animal

# Invariance is required for mutable types
val cat_cell: Cell<Cat> = Cell(Cat())
val animal_cell: Cell<Animal> = cat_cell  # ERROR: could write Dog into cat_cell!

# Contravariance for function parameters
val feed_animal: fn(Animal) -> () = \a: a.eat()
val feed_cat: fn(Cat) -> () = feed_animal  # OK: can pass Cat to fn expecting Animal
```

**Liskov Substitution Principle:**
- Covariant: Producer (output) - can substitute more specific for less specific
- Contravariant: Consumer (input) - can substitute less specific for more specific
- Invariant: Both producer and consumer - no substitution

---

## Current Status

### Simple's Capabilities

Simple has reference capabilities (`mut T`, `iso T`) but no variance inference:

```simple
struct Box<T>:           # Is T covariant? Unknown.
    value: T

struct Cell<T>:          # Is T invariant? Unknown.
    value: mut T

fn map<T, U>(list: [T], f: fn(T) -> U) -> [U]
    # Is T contravariant in f? Is U covariant? Unknown.
```

### Missing Features

1. ✅ **Already have:** Subtyping primitives (from Phase 5)
2. ❌ **Need:** Variance calculation for type parameters
3. ❌ **Need:** Variance checking at use sites
4. ❌ **Need:** Variance annotations (`+T`, `-T`, `T`)

---

## Phase Breakdown

### Phase 6A: Variance Representation (2 hours)

**Goal:** Define variance types and annotations

**Data Structures:**

```simple
# Variance of a type parameter
enum Variance:
    Covariant        # +T (producer, read-only)
    Contravariant    # -T (consumer, input)
    Invariant        # T (both, mutable)
    Bivariant        # ±T (unused)

# Variance annotation in type definitions
class TypeParamDef:
    name: Symbol
    kind: Kind
    variance: Variance      # NEW: explicit or inferred

# Variance environment
class VarianceEnv:
    type_params: text       # Dict<Symbol, Variance>

    fn get_variance(param: Symbol) -> Variance
    me set_variance(param: Symbol, variance: Variance)
    fn combine(v1: Variance, v2: Variance) -> Variance  # Composition rule
```

**Variance Composition Rules:**

| Context | Covariant → | Contravariant → | Invariant → |
|---------|-------------|-----------------|-------------|
| Covariant | Covariant | Contravariant | Invariant |
| Contravariant | Contravariant | Covariant | Invariant |
| Invariant | Invariant | Invariant | Invariant |

**Examples:**

```simple
# Covariant context (return type)
fn get_box() -> Box<T>:   # T is covariant

# Contravariant context (parameter)
fn process(x: fn(T) -> U):  # T is contravariant, U is covariant

# Nested variance
fn higher(f: fn(fn(T) -> U) -> V):
    # T: contravariant → contravariant → covariant (flips twice)
    # U: covariant → contravariant → contravariant (flips once)
    # V: covariant (no flip)
```

**Tests:**
- Variance enum creation
- Variance composition (covariant + contravariant = invariant)
- Variance composition (contravariant + contravariant = covariant)
- TypeParamDef with variance
- VarianceEnv basic operations

---

### Phase 6B: Variance Inference Algorithm (3 hours)

**Goal:** Calculate variance for each type parameter from struct/class definition

**Algorithm:**

```simple
class VarianceInference:
    type_defs: text     # Dict<Symbol, TypeDef>
    variances: text     # Dict<Symbol, Dict<Symbol, Variance>>  # type name → param → variance

    me infer_variance(type_def: TypeDef) -> Dict<Symbol, Variance>:
        """
        Infer variance for all type parameters in a type definition

        Algorithm:
        1. Initialize all parameters to Bivariant (unused)
        2. Walk through type definition:
           - Fields: analyze field types
           - Methods: analyze parameter/return types
        3. Combine variances using composition rules
        4. Fixed-point iteration for recursive types
        """
        var variances = {}

        # Initialize to bivariant (unused)
        for param in type_def.type_params:
            variances[param.name] = Variance.Bivariant

        # Analyze fields
        for field in type_def.fields:
            val field_variances = self.analyze_type(
                field.ty,
                context: Variance.Covariant,  # Fields are in covariant position
                variances: variances
            )

            # Combine with existing
            for param, v in field_variances:
                variances[param] = self.combine_variance(variances[param], v)

        # Analyze methods
        for method in type_def.methods:
            # Parameters are contravariant
            for param in method.params:
                val param_variances = self.analyze_type(
                    param.ty,
                    context: Variance.Contravariant,
                    variances: variances
                )
                for p, v in param_variances:
                    variances[p] = self.combine_variance(variances[p], v)

            # Return type is covariant
            val return_variances = self.analyze_type(
                method.return_ty,
                context: Variance.Covariant,
                variances: variances
            )
            for p, v in return_variances:
                variances[p] = self.combine_variance(variances[p], v)

        variances

    me analyze_type(ty: HirType, context: Variance, variances: Dict<Symbol, Variance>) -> Dict<Symbol, Variance>:
        """
        Analyze a type in a given variance context

        Returns: Dict mapping type parameters to their variance in this type
        """
        match ty:
            case TypeVariable(name):
                # Found usage of type parameter
                {name: context}

            case Arrow(from, to):
                # Function type: parameter is contravariant, return is covariant
                val from_vars = self.analyze_type(
                    from,
                    context: self.flip_variance(context),  # Flip for parameter
                    variances: variances
                )
                val to_vars = self.analyze_type(
                    to,
                    context: context,  # Same context for return
                    variances: variances
                )
                self.merge_variance_dicts(from_vars, to_vars)

            case Generic(name, args):
                # Look up variance of the generic type's parameters
                val type_variances = self.get_type_variances(name)

                var result = {}
                for i, arg in args.enumerate():
                    val param_variance = type_variances[i]
                    val combined_context = self.compose_variance(context, param_variance)

                    val arg_vars = self.analyze_type(arg, combined_context, variances)
                    result = self.merge_variance_dicts(result, arg_vars)

                result

            case _:
                {}  # No type parameters used

    fn flip_variance(v: Variance) -> Variance:
        """Flip variance (for contravariant position)"""
        match v:
            case Covariant: Variance.Contravariant
            case Contravariant: Variance.Covariant
            case Invariant: Variance.Invariant
            case Bivariant: Variance.Bivariant

    fn compose_variance(outer: Variance, inner: Variance) -> Variance:
        """Compose two variance contexts"""
        match (outer, inner):
            case (Covariant, v): v                    # co + v = v
            case (Contravariant, v): flip_variance(v) # contra + v = flip(v)
            case (Invariant, _): Variance.Invariant   # inv + v = inv
            case (Bivariant, _): Variance.Bivariant   # bi + v = bi

    fn combine_variance(v1: Variance, v2: Variance) -> Variance:
        """Combine two variance constraints (intersection)"""
        match (v1, v2):
            case (Bivariant, v): v           # unused + v = v
            case (v, Bivariant): v           # v + unused = v
            case (Covariant, Covariant): Variance.Covariant
            case (Contravariant, Contravariant): Variance.Contravariant
            case _: Variance.Invariant       # Conflict → invariant
```

**Examples:**

```simple
# Example 1: Box<T> (covariant)
struct Box<T>:
    value: T              # T in covariant position (field)

# Inference:
# - value: T field → T is covariant
# - Result: T = Covariant

# Example 2: Cell<T> (invariant)
struct Cell<T>:
    value: mut T          # mut T is invariant

# Inference:
# - value: mut T → T is invariant (mutable reference)
# - Result: T = Invariant

# Example 3: Function type (contravariant/covariant)
type Fn<T, U> = fn(T) -> U

# Inference:
# - Parameter T → contravariant position
# - Return U → covariant position
# - Result: T = Contravariant, U = Covariant

# Example 4: Nested variance
struct Processor<T>:
    handler: fn(T) -> ()

# Inference:
# - handler field → covariant context
# - fn(T) → T in contravariant position within covariant field
# - Combined: T = contravariant
# - Result: T = Contravariant
```

**Tests:**
- Infer Box<T> = Covariant
- Infer Cell<T> = Invariant
- Infer fn(T) -> U = (Contravariant, Covariant)
- Nested variance (Box<fn(T) -> U>)
- Multiple parameters with different variances
- Recursive types (fixed-point iteration)

---

### Phase 6C: Variance Checking (2 hours)

**Goal:** Validate variance at use sites (subtyping, assignments)

**Subtyping Rules:**

```simple
class VarianceChecker:
    variance_env: VarianceEnv

    fn check_subtype(sub: HirType, sup: HirType) -> bool:
        """
        Check if sub <: sup (sub is a subtype of sup)

        Uses variance to determine if generic types are subtypes
        """
        match (sub, sup):
            case (Generic(name1, args1), Generic(name2, args2)):
                if name1 != name2:
                    return false

                # Check type arguments according to variance
                val variances = self.variance_env.get_type_variances(name1)

                for i, (arg1, arg2) in args1.zip(args2).enumerate():
                    val variance = variances[i]

                    match variance:
                        case Covariant:
                            # F<A> <: F<B> if A <: B
                            if not self.check_subtype(arg1, arg2):
                                return false

                        case Contravariant:
                            # F<A> <: F<B> if B <: A (flipped!)
                            if not self.check_subtype(arg2, arg1):
                                return false

                        case Invariant:
                            # F<A> <: F<B> only if A = B
                            if not self.types_equal(arg1, arg2):
                                return false

                        case Bivariant:
                            # F<A> <: F<B> always (unused parameter)
                            ()

                true

            case _:
                # Delegate to standard subtyping rules
                self.check_structural_subtype(sub, sup)
```

**Examples:**

```simple
# Example 1: Covariant Box
val cat_box: Box<Cat> = Box(Cat())
val animal_box: Box<Animal> = cat_box  # OK: Box is covariant

# Check: Box<Cat> <: Box<Animal>?
# - Box has variance: T = Covariant
# - Check: Cat <: Animal? Yes.
# - Result: OK

# Example 2: Invariant Cell
val cat_cell: Cell<Cat> = Cell(Cat())
val animal_cell: Cell<Animal> = cat_cell  # ERROR: Cell is invariant

# Check: Cell<Cat> <: Cell<Animal>?
# - Cell has variance: T = Invariant
# - Check: Cat = Animal? No.
# - Result: ERROR

# Example 3: Contravariant function
val feed_animal: fn(Animal) -> () = \a: a.eat()
val feed_cat: fn(Cat) -> () = feed_animal  # OK: contravariant parameter

# Check: fn(Animal) -> () <: fn(Cat) -> ()?
# - Function has variance: T = Contravariant (parameter)
# - Check (flipped): Cat <: Animal? Yes.
# - Result: OK
```

**Tests:**
- Covariant subtyping (Box<Cat> <: Box<Animal>)
- Invariant rejection (Cell<Cat> not <: Cell<Animal>)
- Contravariant function parameters
- Nested variance checking
- Error messages for variance violations

---

### Phase 6D: Integration & Advanced Cases (1 hour)

**Goal:** Integrate variance checking with type checker, handle edge cases

**Integration Points:**

1. **Type Checker Integration:**
```simple
# In type_infer.spl
me check_assignment(lhs_ty: HirType, rhs_ty: HirType) -> bool:
    # Use variance checker for subtyping
    if self.variance_checker.check_subtype(rhs_ty, lhs_ty):
        return true

    self.error("Type mismatch: cannot assign {rhs_ty} to {lhs_ty}")
    false
```

2. **Method Call Validation:**
```simple
# Check method receiver variance
me check_method_call(receiver_ty: HirType, method: Method) -> bool:
    val expected_receiver = method.receiver_ty

    # Check receiver type is valid subtype
    if self.variance_checker.check_subtype(receiver_ty, expected_receiver):
        return true

    self.error("Invalid receiver type for method")
    false
```

3. **Generic Instantiation:**
```simple
# Validate variance when instantiating generic types
me instantiate_generic(name: Symbol, args: [HirType]) -> HirType:
    val type_def = self.get_type_def(name)

    # Check variance annotations match inferred variance
    for param, arg in type_def.type_params.zip(args):
        if param.variance is explicit:
            val inferred = self.variance_env.get_variance(name, param.name)
            if param.variance != inferred:
                self.warn("Explicit variance annotation {param.variance} doesn't match inferred {inferred}")

    HirType.Generic(name: name, args: args)
```

**Advanced Cases:**

1. **Phantom Type Parameters:**
```simple
# Type parameter not used in fields/methods → bivariant
struct Marker<T>:
    # T is not used → bivariant
    marker: ()

# Phantom<Cat> <: Phantom<Animal> (always, T is unused)
```

2. **Lifetime-Like Variance (Future):**
```simple
# Reference with lifetime variance
struct Ref<'a, T>:
    value: &'a T

# 'a is covariant (longer lifetime <: shorter lifetime)
# T is covariant (read-only reference)
```

3. **Trait Object Variance:**
```simple
# Trait objects are invariant in most cases
val cat_trait: dyn Animal = Cat()  # OK if dyn Animal = invariant
```

**Tests:**
- Integration with type checker
- Method call validation
- Generic instantiation
- Phantom types (bivariant)
- Error messages

---

## Examples

### Example 1: Container Types

```simple
# Immutable container (covariant)
struct Vec<T>:
    data: [T]
    len: i64

# Variance inference:
# - data: [T] → T in covariant position
# - len: i64 → no variance
# - Result: T = Covariant

# Usage:
val cats: Vec<Cat> = Vec([Cat(), Cat()])
val animals: Vec<Animal> = cats  # OK: Vec is covariant
```

### Example 2: Mutable Container (Invariant)

```simple
# Mutable container (invariant)
struct VecMut<T>:
    data: mut [T]
    len: i64

# Variance inference:
# - data: mut [T] → T in invariant position (mutable)
# - len: i64 → no variance
# - Result: T = Invariant

# Usage:
val cats: VecMut<Cat> = VecMut([Cat()])
val animals: VecMut<Animal> = cats  # ERROR: VecMut is invariant
# Reason: Could do animals.push(Dog()), breaking type safety for cats
```

### Example 3: Function Types

```simple
# Function type (contravariant parameter, covariant return)
type Handler<T, U> = fn(T) -> U

# Variance inference:
# - T in parameter position → contravariant
# - U in return position → covariant
# - Result: T = Contravariant, U = Covariant

# Usage:
val process_animal: Handler<Animal, i64> = \a: a.age()
val process_cat: Handler<Cat, i64> = process_animal  # OK: contravariant T

val make_cat: Handler<(), Cat> = \: Cat()
val make_animal: Handler<(), Animal> = make_cat  # OK: covariant U
```

### Example 4: Nested Variance

```simple
# Nested generic type
struct Container<T>:
    get_value: fn() -> T
    set_value: fn(T) -> ()

# Variance inference:
# - get_value: fn() -> T → T in covariant position (return)
# - set_value: fn(T) -> () → T in contravariant position (parameter)
# - Combined: T = Invariant (both covariant and contravariant)
# - Result: T = Invariant

# Usage:
val cat_container: Container<Cat> = Container(...)
val animal_container: Container<Animal> = cat_container  # ERROR: invariant
```

### Example 5: Recursive Types

```simple
# Recursive type with variance
enum Tree<T>:
    Leaf(value: T)
    Node(left: Tree<T>, right: Tree<T>)

# Variance inference:
# - Leaf.value: T → covariant
# - Node.left: Tree<T> → T appears in covariant position recursively
# - Node.right: Tree<T> → T appears in covariant position recursively
# - Result: T = Covariant (fixed-point iteration)

# Usage:
val cat_tree: Tree<Cat> = Tree.Leaf(Cat())
val animal_tree: Tree<Animal> = cat_tree  # OK: Tree is covariant
```

---

## Testing Strategy

### Test Categories

1. **Variance Representation (Phase 6A):**
   - Variance enum operations
   - Composition rules (all combinations)
   - VarianceEnv operations

2. **Variance Inference (Phase 6B):**
   - Simple types (Box, Cell)
   - Function types
   - Nested variance
   - Multiple parameters
   - Recursive types

3. **Variance Checking (Phase 6C):**
   - Covariant subtyping
   - Invariant rejection
   - Contravariant parameters
   - Error messages

4. **Integration (Phase 6D):**
   - Type checker integration
   - Method calls
   - Generic instantiation
   - Phantom types

### Test Count: ~25 tests

---

## Performance Characteristics

### Time Complexity

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Variance inference | O(n × m) | n = fields/methods, m = type nesting depth |
| Variance checking | O(d) | d = type argument depth |
| Variance composition | O(1) | Lookup table |

### Space Complexity

| Structure | Complexity | Notes |
|-----------|-----------|-------|
| VarianceEnv | O(t × p) | t = type count, p = avg params per type |
| Variance cache | O(t × p) | Memoized results |

---

## Integration with Existing Systems

### 1. Trait System (Phase 2)

Variance applies to trait type parameters:

```simple
trait Functor<F>:
    fn map<A, B>(fa: F<A>, f: fn(A) -> B) -> F<B>

# F must be covariant for map to be safe
# Check: F's variance matches Functor requirements
```

### 2. Associated Types (Phase 4)

Associated types can have variance:

```simple
trait Iterator:
    type Item  # Covariant (output position)

# Vec<T>::Iterator = VecIter<T>
# VecIter is covariant if T is covariant in Vec
```

### 3. Higher-Rank Types (Phase 5)

Variance interacts with quantifiers:

```simple
# forall T. fn(T) -> T
# T appears in both covariant and contravariant positions → invariant
```

---

## Limitations

### 1. Manual Annotations Required (Initially)

Current implementation requires explicit variance annotations for verification:

```simple
struct Box<+T>:  # Explicit covariant annotation
    value: T
```

**Future:** Infer automatically, annotations for override/verification only.

### 2. No Lifetime Variance (Yet)

Lifetimes not implemented, so lifetime variance deferred:

```simple
struct Ref<'a, T>:  # 'a variance not tracked
    ptr: &'a T
```

**Future:** Add lifetime system with covariant/contravariant lifetimes.

### 3. No Higher-Kinded Variance

Variance for type constructors (kind `* -> *`) not supported:

```simple
# Can't express: F<+A> for any F
trait Functor<F<_>>:
    fn map<A, B>(fa: F<A>, f: fn(A) -> B) -> F<B>
```

**Future:** Add higher-kinded types with variance.

---

## Next Steps

After Phase 6:
1. **Phase 7:** Macro Type Checking (15h)
2. **Phase 8:** Const Keys (6h)
3. **Phase 9:** SIMD Complete (4h)

---

## File Structure

```
src/compiler/
  variance_phase6a.spl         # Variance representation (2h)
  variance_phase6b.spl         # Variance inference (3h)
  variance_phase6c.spl         # Variance checking (2h)
  variance_phase6d.spl         # Integration (1h)

doc/plan/
  variance_inference_implementation_plan.md  # This file

doc/report/
  variance_inference_complete_2026-02-03.md  # To be created
```

---

## Success Criteria

✅ All 4 phases implemented
✅ 25+ tests passing
✅ Variance inferred for all generic types
✅ Subtyping respects variance
✅ Integration with type checker
✅ Error messages for variance violations

---

**Status:** Ready to implement
**Next:** Phase 6A - Variance Representation (2 hours)
