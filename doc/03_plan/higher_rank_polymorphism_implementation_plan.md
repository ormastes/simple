# Higher-Rank Polymorphism Implementation Plan

**Phase:** 5 (Rust Feature Parity Roadmap)
**Estimated Time:** 12 hours
**Status:** 🚧 In Progress
**Dependencies:**
- Phase 2 (Trait System) ✅ Complete
- Phase 4 (Associated Types) ✅ Complete

---

## Overview

Higher-rank polymorphism (HRP) allows universal quantification (`forall`) in non-top-level positions, enabling:
- Functions that accept polymorphic functions as arguments
- Trait methods with generic type parameters
- Existential types (dual of forall)
- Rank-2+ types (nested foralls)

**Key Difference from Rank-1:**

```simple
# Rank-1 (standard generics):
fn map<T, U>(f: fn(T) -> U, items: [T]) -> [U]
# forall T, U. (fn(T) -> U, [T]) -> [U]

# Rank-2 (higher-rank):
fn apply_to_both(f: forall T. fn(T) -> T) -> (i32, text)
# (forall T. fn(T) -> T) -> (i32, text)
# Note: forall is INSIDE the function type, not at top level
```

**Use Cases:**
- ST monad (safe mutable state)
- Callback functions that must work for all types
- Trait methods with independent type parameters
- Church encodings and continuations

---

## Architecture

### New Components

```
src/compiler/
├── trait_def.spl              # ✅ Exists
├── trait_solver.spl           # ✅ Exists
├── associated_types_phase4d.spl  # ✅ Exists
└── higher_rank_poly.spl       # 🆕 NEW (Phase 5)
```

### Data Structures

```simple
# In higher_rank_poly.spl - NEW

enum Quantifier:
    Forall(var: TyVar, kind: Kind)
    Exists(var: TyVar, kind: Kind)

class PolyType:
    """
    Polymorphic type with explicit quantifiers

    Examples:
        forall T. T -> T
        forall T, U. (T, U) -> U
        forall T. (forall U. fn(T, U) -> U) -> T
    """
    quantifiers: [Quantifier]
    body: HirType

enum HirType:
    # ... existing variants ...
    Forall(quantifiers: [Quantifier], body: HirType)  # NEW
    Exists(var: TyVar, kind: Kind, body: HirType)     # NEW
    Skolem(id: i64)  # NEW: Skolem type for instantiation

class QuantifierContext:
    """
    Tracks quantifier scopes during type checking

    Maintains:
    - Currently bound type variables
    - Skolem constant generation
    - Scope nesting levels
    """
    bound_vars: Dict<TyVar, QuantifierLevel>
    skolem_counter: i64
    scope_level: i64

class HigherRankUnifier:
    """
    Extended unification for higher-rank types

    Algorithm:
    - Instantiation: forall T. f(T) ~> f(?α) where ?α is fresh
    - Skolemization: forall T. τ ~> τ[T := sk_i] where sk_i is rigid
    - Deep skolemization for nested foralls
    """
```

---

## Implementation Phases

### Phase 5A: Quantifier Representation (3 hours)

**File:** NEW `src/compiler/higher_rank_poly.spl` (Phase 5A)

**Tasks:**
1. Add `Quantifier` enum (Forall/Exists)
2. Add `PolyType` class
   - quantifiers, body fields
   - `to_string()` method
   - `is_monomorphic()` check
3. Extend `HirType` with:
   - `Forall(quantifiers, body)` variant
   - `Exists(var, kind, body)` variant
   - `Skolem(id)` variant for rigid type variables
4. Add kind system basics:
   ```simple
   enum Kind:
       Star  # * (type of types)
       Arrow(from: Kind, to: Kind)  # * -> * (type constructors)
   ```
5. Add `TyVar` representation:
   ```simple
   class TyVar:
       id: i64
       name: Symbol
       kind: Kind
   ```

**Examples:**
```simple
# id function: forall T. T -> T
val id_type = PolyType(
    quantifiers: [Quantifier.Forall(TyVar(id: 0, name: "T", kind: Kind.Star))],
    body: HirType.Arrow(
        from: HirType.Var(id: 0),
        to: HirType.Var(id: 0)
    )
)

# compose: forall A, B, C. (B -> C) -> (A -> B) -> (A -> C)
val compose_type = PolyType(
    quantifiers: [
        Quantifier.Forall(TyVar(id: 0, name: "A", kind: Kind.Star)),
        Quantifier.Forall(TyVar(id: 1, name: "B", kind: Kind.Star)),
        Quantifier.Forall(TyVar(id: 2, name: "C", kind: Kind.Star))
    ],
    body: Arrow(Arrow(Var(1), Var(2)), Arrow(Arrow(Var(0), Var(1)), Arrow(Var(0), Var(2))))
)
```

**Tests:**
- Basic forall type creation
- Multiple quantifiers
- Nested forall types
- Exists types
- Skolem types
- Kind checking

---

### Phase 5B: Quantifier Context & Scoping (3 hours)

**File:** Extend `src/compiler/higher_rank_poly.spl` (Phase 5B)

**Tasks:**
1. Add `QuantifierLevel` for scope tracking
   ```simple
   class QuantifierLevel:
       level: i64
       is_rigid: bool  # Skolem vs inference variable
   ```
2. Add `QuantifierContext` class
   - `me enter_forall()` - push scope
   - `me exit_forall()` - pop scope
   - `me bind_var(var: TyVar, level: QuantifierLevel)`
   - `fn is_bound(var: TyVar) -> bool`
   - `fn get_level(var: TyVar) -> QuantifierLevel`
   - `me fresh_skolem() -> HirType.Skolem`
3. Implement scope tracking algorithm:
   ```simple
   me enter_forall() -> i64:
       self.scope_level = self.scope_level + 1
       self.scope_level

   me exit_forall():
       # Remove bindings at current level
       var to_remove = []
       for (var, level) in self.bound_vars:
           if level.level == self.scope_level:
               to_remove.push(var)
       for var in to_remove:
           # Remove from dict
       self.scope_level = self.scope_level - 1
   ```

**Examples:**
```simple
# Nested scoping:
# forall T. (forall U. fn(T, U) -> U) -> T

val ctx = QuantifierContext.new()

# Outer forall
val level1 = ctx.enter_forall()
ctx.bind_var(TyVar("T"), QuantifierLevel(level: level1, is_rigid: false))

# Inner forall
val level2 = ctx.enter_forall()
ctx.bind_var(TyVar("U"), QuantifierLevel(level: level2, is_rigid: false))

# T is bound at level 1
# U is bound at level 2

ctx.exit_forall()  # Exit U scope
ctx.exit_forall()  # Exit T scope
```

**Tests:**
- Scope nesting
- Bind/lookup variables
- Fresh skolem generation
- Scope exit cleanup
- Level tracking

---

### Phase 5C: Instantiation & Skolemization (4 hours)

**File:** Extend `src/compiler/higher_rank_poly.spl` (Phase 5C)

**Tasks:**
1. Add `HigherRankUnifier` class
2. Implement **instantiation** (forall elimination):
   ```simple
   fn instantiate(poly_type: PolyType) -> HirType:
       """
       Instantiate quantifiers with fresh inference variables

       forall T, U. τ ~> τ[T := ?α, U := ?β]
       """
       var subst = {}
       for quantifier in poly_type.quantifiers:
           match quantifier:
               case Forall(var, kind):
                   val fresh_var = self.fresh_inference_var(kind)
                   subst[var.id] = fresh_var

       self.substitute(poly_type.body, subst)
   ```
3. Implement **skolemization** (forall checking):
   ```simple
   fn skolemize(poly_type: PolyType) -> HirType:
       """
       Skolemize quantifiers with rigid type constants

       forall T, U. τ ~> τ[T := sk_0, U := sk_1]

       Skolems are rigid - cannot be unified with anything
       """
       var subst = {}
       for quantifier in poly_type.quantifiers:
           match quantifier:
               case Forall(var, kind):
                   val skolem = self.ctx.fresh_skolem()
                   subst[var.id] = skolem

       self.substitute(poly_type.body, subst)
   ```
4. Implement **deep skolemization** (rank-2+):
   ```simple
   fn deep_skolemize(ty: HirType) -> HirType:
       """
       Skolemize nested foralls

       Example:
           (forall T. T -> T) -> i32
           ~> (sk_0 -> sk_0) -> i32

       Algorithm:
       - Traverse type structure
       - Skolemize foralls in negative positions (contravariant)
       - Instantiate foralls in positive positions (covariant)
       """
       match ty:
           case Forall(quantifiers, body):
               # Negative position - skolemize
               self.skolemize(PolyType(quantifiers, body))

           case Arrow(from, to):
               # from is contravariant (negative)
               # to is covariant (positive)
               val from_skolem = self.deep_skolemize(from)
               val to_inst = self.deep_instantiate(to)
               HirType.Arrow(from: from_skolem, to: to_inst)

           case _:
               ty
   ```

**Examples:**
```simple
# Example 1: Simple instantiation
# forall T. T -> T
# ~> ?α -> ?α (where ?α is fresh inference variable)

# Example 2: Skolemization
# forall T. T -> T
# ~> sk_0 -> sk_0 (where sk_0 is rigid)

# Example 3: Rank-2 type
# (forall T. T -> T) -> i32
# When checking function argument:
#   - Expect: forall T. T -> T
#   - Got: some_func with type ?α -> ?α
#   - Skolemize: sk_0 -> sk_0
#   - Unify: ?α ~ sk_0 (sets ?α = sk_0)
```

**Tests:**
- Simple instantiation
- Simple skolemization
- Deep skolemization (rank-2)
- Nested foralls
- Inference variable generation
- Skolem rigidity

---

### Phase 5D: Higher-Rank Unification (2 hours)

**File:** Extend `src/compiler/higher_rank_poly.spl` (Phase 5D)

**Tasks:**
1. Extend unification algorithm for higher-rank types:
   ```simple
   fn unify(ty1: HirType, ty2: HirType) -> bool:
       match (ty1, ty2):
           # Forall left: instantiate
           case (Forall(quantifiers, body), _):
               val inst = self.instantiate(PolyType(quantifiers, body))
               self.unify(inst, ty2)

           # Forall right: skolemize
           case (_, Forall(quantifiers, body)):
               val skolem = self.skolemize(PolyType(quantifiers, body))
               self.unify(ty1, skolem)

           # Skolem: rigid, only unifies with itself
           case (Skolem(id1), Skolem(id2)):
               id1 == id2

           # Skolem cannot unify with inference variable
           case (Skolem(_), Var(_)):
               false
           case (Var(_), Skolem(_)):
               false

           # ... existing unification rules ...
   ```
2. Add occurs check for skolems:
   ```simple
   fn occurs_check(var: TyVar, ty: HirType) -> bool:
       # Check if var occurs in ty
       # Also check if any skolem escapes its scope
   ```
3. Add subsumption checking:
   ```simple
   fn subsumes(poly1: PolyType, poly2: PolyType) -> bool:
       """
       Check if poly1 is more polymorphic than poly2

       forall T. T -> T  subsumes  i32 -> i32
       forall T, U. (T, U) -> U  subsumes  forall U. (i32, U) -> U
       """
       # Instantiate poly2
       val inst2 = self.instantiate(poly2)

       # Skolemize poly1
       val skolem1 = self.skolemize(poly1)

       # Check if skolem1 unifies with inst2
       self.unify(skolem1, inst2)
   ```

**Examples:**
```simple
# Example 1: Function taking polymorphic function
fn apply_to_int(f: forall T. fn(T) -> T) -> i32:
    f(42)

# Type checking:
# - f has type: forall T. fn(T) -> T
# - Instantiate at call site: f<i32>
# - Type of f(42): i32 -> i32

# Example 2: ST monad (classic rank-2 example)
fn run_st<A>(action: forall S. fn(ST<S, A>) -> A) -> A:
    # S is existential - prevents state from escaping
    action(ST.new())

# Type: forall A. (forall S. fn(ST<S, A>) -> A) -> A
# Rank-2: forall is nested inside function argument
```

**Tests:**
- Basic higher-rank unification
- Forall instantiation in unify
- Forall skolemization in unify
- Skolem rigidity check
- Subsumption checking
- ST monad example

---

## Testing Strategy

### Unit Tests (25+ tests)

**Phase 5A Tests (6 tests):**
- `test_quantifier_basic()` - Create forall/exists
- `test_poly_type_creation()` - PolyType with quantifiers
- `test_nested_forall()` - Nested quantifiers
- `test_skolem_type()` - Skolem constant
- `test_kind_basic()` - Kind representation
- `test_type_var()` - TyVar with kind

**Phase 5B Tests (5 tests):**
- `test_context_scoping()` - Enter/exit forall
- `test_bind_lookup()` - Bind and lookup vars
- `test_fresh_skolem()` - Generate skolems
- `test_nested_scopes()` - Nested forall scopes
- `test_scope_cleanup()` - Exit removes bindings

**Phase 5C Tests (7 tests):**
- `test_instantiate_basic()` - Simple instantiation
- `test_instantiate_multiple()` - Multiple quantifiers
- `test_skolemize_basic()` - Simple skolemization
- `test_skolemize_rigidity()` - Skolems are rigid
- `test_deep_skolemize_rank2()` - Rank-2 type
- `test_deep_skolemize_nested()` - Nested foralls
- `test_contravariance()` - Negative position skolemization

**Phase 5D Tests (7 tests):**
- `test_unify_forall_left()` - Instantiate left forall
- `test_unify_forall_right()` - Skolemize right forall
- `test_unify_skolem_rigid()` - Skolem rigidity
- `test_unify_rank2()` - Rank-2 unification
- `test_subsumption_basic()` - Subsumption check
- `test_subsumption_rank2()` - Rank-2 subsumption
- `test_st_monad()` - ST monad type checking

---

## Examples

### Example 1: Identity Function

```simple
# Type: forall T. T -> T
fn id<T>(x: T) -> T:
    x

# Polymorphic type
val id_type = PolyType(
    quantifiers: [Quantifier.Forall(TyVar("T"))],
    body: Arrow(Var("T"), Var("T"))
)

# Instantiation at call site
val result = id(42)  # T = i32
```

### Example 2: Rank-2 Function

```simple
# Type: (forall T. T -> T) -> (i32, text)
fn apply_to_both(f: forall T. fn(T) -> T) -> (i32, text):
    (f(42), f("hello"))

# Type checking:
# - f has type: forall T. T -> T
# - At f(42): instantiate T = i32
# - At f("hello"): instantiate T = text
# - Return type: (i32, text)
```

### Example 3: ST Monad

```simple
# State thread monad (prevents state from escaping)
type ST<S, A>

fn run_st<A>(action: forall S. fn(ST<S, A>) -> A) -> A:
    # S is universally quantified INSIDE the function type
    # This prevents the state from escaping
    action(ST.new())

# Usage:
val result = run_st(fn(st):
    val r = st.new_ref(0)
    r.write(42)
    r.read()
)
# result: i32 = 42
# r cannot escape - type error if attempted
```

### Example 4: Church Encoding

```simple
# Church boolean: forall T. T -> T -> T
type ChurchBool = forall T. fn(T, T) -> T

fn church_true<T>(t: T, f: T) -> T:
    t

fn church_false<T>(t: T, f: T) -> T:
    f

# Church numerals: forall T. (T -> T) -> T -> T
type ChurchNum = forall T. fn(fn(T) -> T, T) -> T
```

---

## Integration Points

### Type Checker Integration

```simple
# In type_checker.spl
fn check_function_call(func_type: HirType, arg_type: HirType) -> HirType:
    match func_type:
        case Forall(quantifiers, body):
            # Instantiate quantifiers
            val inst_type = higher_rank_unifier.instantiate(PolyType(quantifiers, body))
            check_function_call(inst_type, arg_type)

        case Arrow(param_type, return_type):
            # Check param
            match param_type:
                case Forall(_, _):
                    # Argument must be polymorphic
                    # Skolemize and unify
                    val skolem_param = higher_rank_unifier.skolemize_type(param_type)
                    unify(arg_type, skolem_param)
                case _:
                    unify(arg_type, param_type)

            return_type
```

### Trait Method Integration

```simple
# Trait with generic method
trait Visitor:
    fn visit<T>(self, value: T)  # Method has own type parameter

# This is rank-2:
# Visitor = { visit: forall T. fn(T) }
```

---

## Performance Considerations

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Instantiation | O(quantifiers) | Linear in quantifier count |
| Skolemization | O(quantifiers) | Linear in quantifier count |
| Deep skolemization | O(type_size) | Traverse entire type |
| Unification | O(type_size) | With occurs check |
| Subsumption | O(type_size × quantifiers) | Instantiate + unify |

**Optimization Opportunities:**
- Cache instantiated types
- Use structural sharing for type terms
- Lazy skolemization (only when needed)
- Bidirectional type checking to reduce inference

---

## Future Extensions

### Impredicative Polymorphism

```simple
# Allow forall in any position
val poly_list: [forall T. T -> T] = [id, id, id]
# Requires: bidirectional type checking or explicit type annotations
```

### Dependent Types (Limited)

```simple
# Type-level functions
type Vec<n: Nat, T>

fn concat<n: Nat, m: Nat, T>(v1: Vec<n, T>, v2: Vec<m, T>) -> Vec<n + m, T>
```

---

## Success Criteria

✅ **Phase 5A Complete:**
- Quantifier and PolyType classes
- Extended HirType with Forall/Exists/Skolem
- Kind system basics
- 6 tests passing

✅ **Phase 5B Complete:**
- QuantifierContext with scope tracking
- Enter/exit forall
- Variable binding and lookup
- 5 tests passing

✅ **Phase 5C Complete:**
- Instantiation algorithm
- Skolemization algorithm
- Deep skolemization for rank-2+
- 7 tests passing

✅ **Phase 5D Complete:**
- Extended unification for higher-rank types
- Subsumption checking
- ST monad example working
- 7 tests passing

✅ **Overall Success:**
- All 25+ tests passing
- Zero compiler errors
- Examples compile and run
- Ready for compiler integration

---

## Timeline

| Phase | Duration | Cumulative |
|-------|----------|-----------|
| 5A: Quantifier Representation | 3h | 3h |
| 5B: Context & Scoping | 3h | 6h |
| 5C: Instantiation & Skolemization | 4h | 10h |
| 5D: Higher-Rank Unification | 2h | 12h |

**Total: 12 hours**

---

## References

**Completed Phases:**
- Phase 2: Trait System ✅
- Phase 3: Effect System ✅
- Phase 4: Associated Types ✅

**Related Papers:**
- "Practical type inference for arbitrary-rank types" (Peyton Jones et al.)
- "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism" (Dunfield & Krishnaswami)
- "Colored local type inference" (Odersky et al.)

**Related Documentation:**
- Haskell's RankNTypes extension
- Rust's trait object lifetimes (similar escape analysis)

---

**Status:** 🚧 Ready to Start Phase 5A
**Next Step:** Implement Quantifier and PolyType
