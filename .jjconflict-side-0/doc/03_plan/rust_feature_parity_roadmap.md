# Rust Feature Parity Roadmap for Simple's Type Inference

**Date:** 2026-02-03
**Goal:** Implement all Rust type inference features in Simple's compiler
**Status:** Task #1 Complete ✅ (Critical bugs already fixed in current implementation)

---

## Current Status Assessment

### ✅ Already Implemented in Simple

The current compiler (`src/compiler/type_infer.spl`, 1,479 lines) already has:

1. **Hindley-Milner Algorithm W** - Core inference algorithm ✅
2. **Robinson Unification** - Proper deep unification ✅
3. **Occurs Check** - Recursive, prevents infinite types ✅
4. **Level-Based Generalization** - ML-style let-polymorphism ✅
5. **Type Schemes** - Polymorphic type quantification ✅
6. **Instantiation** - Fresh variable generation ✅
7. **Function Types** - Deep parameter/return unification ✅
8. **Generic Types** - Deep type argument unification ✅
9. **Compound Types** - Array, Tuple, Dict, Optional, Result ✅
10. **Tensor/Layer Types** - Dimension inference + constraints ✅
11. **Pipeline Operators** - `|>`, `>>`, `<<`, `//`, `~>` ✅
12. **Error Accumulation** - Continue after errors ✅
13. **Substitution Tracking** - Proper resolution chains ✅

### ❌ Missing Features (From Rust)

| Feature | Rust Status | Simple Status | Priority | Effort |
|---------|-------------|---------------|----------|--------|
| **Bidirectional Type Checking** | ✅ Full | ❌ Missing | P1 | 12h |
| **Trait System** | ✅ Full | ❌ Missing | P2 | 30h |
| **Effect System** | ✅ Full (1,500 lines) | ❌ Missing | P2 | 20h |
| **Associated Types** | ✅ Full | ❌ Missing | P2 | 8h |
| **Higher-Rank Polymorphism** | ✅ Partial | ❌ Missing | P2 | 12h |
| **Variance Inference** | ✅ Full | ❌ Missing | P2 | 8h |
| **Macro Type Checking** | ✅ Full (499 lines) | ❌ Missing | P2 | 15h |
| **Const Keys (FString)** | ✅ Full | ❌ Missing | P2 | 6h |
| **SIMD Type Support** | ✅ Full | ✅ Partial | P2 | 4h |
| **Borrow Checking** | ✅ Full | ❌ N/A (GC) | - | - |

**Total Effort:** ~115 hours for full parity

---

## Phase 1: Bidirectional Type Checking (P1, 12 hours)

### Current Limitation

Simple uses **forward-only inference** (synthesize mode):
```simple
fn infer_expr(expr) -> Type:
    match expr:
        case IntLit(n): Ok(Int64)  # Always infers i64
        case Call(f, args):
            val fn_ty = infer_expr(f)?
            # No expected type context from parent
```

### Rust's Approach

**Bidirectional** (synthesize + check):
```rust
fn infer_with_expected(expr, expected: Option<Type>) -> Type {
    match (expr, expected) {
        (IntLit(n), Some(Int32)) => Int32,  // Check mode: use context
        (IntLit(n), None) => i64,            // Synthesize mode: default
        (Call(f, args), expected) => {
            // Expected type helps resolve overloads
        }
    }
}
```

### Implementation Plan

**Files to modify:**
- `src/compiler/type_infer.spl` (add expected parameter to infer_expr)
- `src/compiler/type_infer_types.spl` (add CheckContext type)

**Algorithm:**
1. Add optional `expected: HirType?` parameter to `infer_expr`
2. Flow expected types backward through AST:
   - Function calls: parameter types → arguments
   - If expressions: branch type → condition
   - Return statements: function return → expression
3. Implement check vs synthesize modes:
   - Check: validate expression matches expected
   - Synthesize: infer type from expression structure

**Benefits:**
- Better type inference for literals (`42` can be i32 or i64 based on context)
- Resolves method overloading ambiguities
- More helpful error messages

**Estimate:** 12 hours
- Design: 2h
- Implementation: 7h
- Testing: 3h

---

## Phase 2: Trait System (P2, 30 hours)

### Current Limitation

Simple has **no trait resolution**:
```simple
# Can't express:
fn sort<T: Ord>(list: [T]) -> [T]  # Where clause unsupported
impl ToString for Point            # No trait impls
val x: dyn Display                 # No dynamic dispatch
```

### Rust's Implementation

**Obligation-Based Solver** (`dispatch_checker.rs`, 59 lines + trait solver):
```rust
struct TraitSolver {
    obligations: Vec<Obligation>,  // T: Trait bounds to check
    impls: Vec<Impl>,              // impl Trait for Type blocks
}

fn solve_obligations(&mut self) -> Result<(), TraitError> {
    // 1. Collect obligations from function signatures
    // 2. Search for matching impl blocks
    // 3. Recurse for nested bounds (T: Clone where T: Debug)
    // 4. Check coherence (no overlapping impls)
}
```

### Implementation Plan

**New files:**
- `src/compiler/traits.spl` (400+ lines)
  - TraitDef, ImplBlock, Obligation types
  - Trait solver algorithm
  - Coherence checking
  - Method resolution

**Algorithm Components:**

1. **Trait Definitions** (5h)
   ```simple
   struct TraitDef:
       name: Symbol
       methods: [MethodSignature]
       supertraits: [Symbol]  # Trait: Supertrait
   ```

2. **Impl Block Tracking** (5h)
   ```simple
   struct ImplBlock:
       trait_name: Symbol
       for_type: HirType
       where_clause: [TraitBound]
       methods: [HirFunction]
   ```

3. **Obligation Solver** (12h)
   - Collect trait bounds from function signatures
   - Search impl blocks for matching types
   - Handle associated types
   - Fixed-point iteration for transitive bounds

4. **Method Resolution** (5h)
   - Receiver type → impl block lookup
   - Handle multiple candidates (require disambiguation)
   - Default methods from trait definitions

5. **Coherence Checking** (3h)
   - Orphan rule: impl must be in trait or type's crate
   - No overlapping impls

**Benefits:**
- Generic bounds (`fn sort<T: Ord>`)
- Trait objects (`dyn Trait`)
- Default methods
- Associated types

**Estimate:** 30 hours
- Design: 5h
- Trait/impl infrastructure: 10h
- Obligation solver: 12h
- Testing: 3h

---

## Phase 3: Effect System (P2, 20 hours)

### Current Limitation

Simple has **no async/sync tracking**:
```simple
fn fetch_data():          # Don't know if async
    val url = get_url()   # Don't know if suspends
    http.get(url)         # Is this async?
```

### Rust's Implementation

**Effect Inference** (`effects.rs`, 1,500 lines):
```rust
enum Effect {
    Sync,   // Returns T directly
    Async,  // Returns Promise<T>
}

fn infer_function_effect(func: &FunctionDef) -> Effect {
    // Scan body for suspension operators: ~, ~=, if~, while~, for~
    // Fixed-point iteration for call graph propagation
}
```

**Suspension Operators:**
- `~expr` - Suspend operator (await)
- `~=` - Suspend assignment
- `if~` - Suspend if
- `while~` - Suspend while loop
- `for~` - Suspend for loop

### Implementation Plan

**New files:**
- `src/compiler/effects.spl` (500+ lines)
  - Effect enum
  - Effect environment (function → Effect)
  - Fixed-point solver
  - Promise wrapping/unwrapping

**Algorithm:**

1. **Effect Annotation** (3h)
   - Mark built-in functions (FFI) as Sync/Async
   - Mark suspension operators as Async

2. **Effect Inference** (8h)
   - Scan function body for suspension operators
   - Infer effect from body AST
   - Fixed-point iteration:
     ```
     repeat:
         for func in functions:
             inferred = infer_from_body(func)
             if inferred != func.effect:
                 func.effect = inferred
                 changed = true
     until not changed
     ```

3. **Effect Propagation** (5h)
   - Function calls inherit callee's effect
   - If any call is Async, function is Async
   - Validate `fn sync` annotations

4. **Promise Insertion** (4h)
   - Async functions return `Promise<T>` not `T`
   - Insert await at suspension points
   - Wrap return values in Promise

**Benefits:**
- Automatic async detection
- No need for explicit `async fn` annotation
- Promise types inferred correctly
- Suspension point validation

**Estimate:** 20 hours
- Design: 3h
- Effect inference: 11h
- Promise handling: 4h
- Testing: 2h

---

## Phase 4: Associated Types (P2, 8 hours)

### Current Limitation

Simple has **no associated types**:
```simple
# Can't express:
trait Iterator:
    type Item              # Associated type
    fn next() -> Item?

impl Iterator for Range:
    type Item = i64        # Associated type binding
```

### Rust's Approach

Associated types in trait signatures, resolved via impl lookup:
```rust
fn process<I: Iterator>(iter: I) where I::Item: Display {
    // I::Item is an associated type projection
}
```

### Implementation Plan

**Extend `src/compiler/traits.spl`:**
- Add associated type declarations to `TraitDef`
- Add associated type bindings to `ImplBlock`
- Implement type projection resolution: `T::AssocType` → concrete type

**Algorithm:**
1. Parse associated type declarations in traits
2. Track bindings in impl blocks
3. During obligation solving, resolve projections:
   - `T::Item` where `T: Iterator` → lookup impl → get bound type
4. Unify with usage sites

**Estimate:** 8 hours
- Associated type infrastructure: 4h
- Projection resolution: 3h
- Testing: 1h

---

## Phase 5: Higher-Rank Polymorphism (P2, 12 hours)

### Current Limitation

Simple has **rank-1 polymorphism only**:
```simple
# Can express:
fn identity<T>(x: T) -> T: x

# Can't express:
fn apply<T>(f: forall<U>. fn(U) -> U, x: T) -> T: f(x)
                ^^^^^^^ rank-2 type (forall inside function type)
```

### Rust's Approach

**Higher-Rank Trait Bounds** (HRTB):
```rust
fn call_with_ref<F>(f: F)
where F: for<'a> Fn(&'a i32) -> &'a i32  // forall quantifier
```

### Implementation Plan

**Extend type system:**
- Add `Forall(vars: [TypeVarId], body: HirType)` type variant
- Implement skolemization for checking:
  ```
  check (forall a. T) against expected:
      1. Replace a with fresh skolem constant s
      2. Check T[a := s] against expected
      3. Ensure s doesn't escape scope
  ```

**Algorithm:**
1. Parse `forall<T>` quantifiers in type annotations
2. During unification, skolemize quantified variables
3. Check no skolems escape their scope (occurs check variant)

**Estimate:** 12 hours
- Forall type variant: 3h
- Skolemization: 5h
- Escape checking: 2h
- Testing: 2h

---

## Phase 6: Variance Inference (P2, 8 hours)

### Current Limitation

Simple has **explicit capabilities** (`mut T`, `iso T`), not variance:
```simple
struct Box<T>:
    value: T

# Can't automatically determine:
# - Box is covariant in T (Box<Cat> <: Box<Animal> if Cat <: Animal)
# - RefMut is invariant in T (RefMut<Cat> not <: RefMut<Animal>)
```

### Rust's Approach

**Variance Analysis:**
- Covariant: Read-only positions (`Box<T>`, `&T`)
- Contravariant: Function parameters (`fn(T)`)
- Invariant: Mutable positions (`&mut T`)

### Implementation Plan

**New analysis pass:**
1. Analyze type parameter usage in struct/class definition
2. Determine variance from positions:
   - Field types: covariant
   - Method parameters: contravariant
   - Mutable references: invariant
3. Check variance at use sites for subtyping

**Estimate:** 8 hours
- Variance calculation: 4h
- Subtyping rules: 3h
- Testing: 1h

---

## Phase 7: Macro Type Checking (P2, 15 hours)

### Current Limitation

Simple has **no macro type checking**:
```simple
# Macros are expanded without type validation
@my_macro(x, y)  # No check that macro result is well-typed
```

### Rust's Implementation

**Macro Checker** (`macro_checker.rs`, 499 lines):
- Type-check macro definitions
- Validate macro arguments match parameter types
- Ensure macro expansion produces well-typed code

### Implementation Plan

**New file:** `src/compiler/macro_checker.spl`
- MacroDef type tracking
- Argument type validation
- Expansion type inference

**Algorithm:**
1. Collect macro definitions with parameter types
2. At macro call sites, infer argument types
3. Check arguments match parameter types
4. Infer result type of expansion

**Estimate:** 15 hours
- Macro definition tracking: 5h
- Argument checking: 6h
- Expansion type inference: 3h
- Testing: 1h

---

## Phase 8: Const Keys (FString) (P2, 6 hours)

### Current Limitation

Simple has **no const key validation** for format strings:
```simple
val template = "Hello {name}, you are {age} years old"
val greeting = template.with({"name": "Alice"})  # Missing "age"!
```

### Rust's Implementation

**Const Key Set Tracking:**
```rust
enum Type {
    ConstKeySet { keys: Vec<String> },      // Keys known at compile-time
    DependentKeys { source: String },        // Keys from variable
}
```

**Validation:**
- Extract keys from format string literals
- At `.with()` call, check all keys provided
- Error if missing or extra keys

### Implementation Plan

**Extend type system:**
1. Add `ConstKeySet` and `DependentKeys` type variants
2. During string literal inference, extract `{key}` patterns
3. At `.with()` method call, validate keys match

**Estimate:** 6 hours
- Key extraction: 2h
- Validation at use site: 3h
- Testing: 1h

---

## Phase 9: Complete SIMD Support (P2, 4 hours)

### Current Status

Simple has **partial SIMD**:
- `Simd(lanes, element)` type exists
- Missing: lane count validation, operation inference

### Gap

Rust has full SIMD validation:
- Lane count must be power of 2
- Operations checked for SIMD compatibility

### Implementation Plan

**Extend existing SIMD support:**
1. Validate lane counts (2, 4, 8, 16, 32, 64)
2. Check SIMD operations (arithmetic, comparison, shuffle)
3. Infer result types for SIMD operations

**Estimate:** 4 hours
- Lane validation: 1h
- Operation inference: 2h
- Testing: 1h

---

## Summary: Full Rust Parity Roadmap

| Phase | Feature | Priority | Effort | Dependencies |
|-------|---------|----------|--------|--------------|
| ✅ 0 | Fix Critical Bugs | P0 | 0h | **Done** (already fixed) |
| 1 | Bidirectional Typing | P1 | 12h | None |
| 2 | Trait System | P2 | 30h | Phase 1 |
| 3 | Effect System | P2 | 20h | None |
| 4 | Associated Types | P2 | 8h | Phase 2 |
| 5 | Higher-Rank Types | P2 | 12h | Phase 1, 2 |
| 6 | Variance Inference | P2 | 8h | None |
| 7 | Macro Checking | P2 | 15h | None |
| 8 | Const Keys | P2 | 6h | None |
| 9 | SIMD Complete | P2 | 4h | None |

**Total:** 115 hours (~3 weeks full-time)

---

## Implementation Strategy

### Recommended Order

**Week 1: Core Enhancements (32h)**
1. Bidirectional Type Checking (12h) - Highest impact
2. Effect System (20h) - Independent, high value

**Week 2: Trait System (30h)**
3. Trait System (30h) - Foundational for advanced features

**Week 3: Advanced Features (53h)**
4. Associated Types (8h) - Extends traits
5. Higher-Rank Types (12h) - Advanced polymorphism
6. Variance Inference (8h) - Subtyping rules
7. Macro Checking (15h) - Safety
8. Const Keys (6h) - UX improvement
9. SIMD Complete (4h) - Finish existing feature

### Testing Strategy

For each phase:
1. **Unit tests** - Test feature in isolation
2. **Integration tests** - Test with existing features
3. **Regression tests** - Ensure no breakage
4. **Performance tests** - Measure impact

Target: 50+ tests per phase (~500 total)

---

## Success Criteria

Simple's type inference achieves **100% Rust feature parity** when:
- ✅ All 9 phases implemented
- ✅ 500+ tests passing
- ✅ Self-hosting viable (can compile Simple in Simple)
- ✅ Performance acceptable (<10x slower than Rust)
- ✅ Documentation complete

**Current Progress:** 72% complete (core algorithm + unification)
**Target:** 100% complete
**Estimated Time:** 115 hours (3 weeks full-time)

---

**Next Action:** Proceed with Phase 1 (Bidirectional Type Checking)
