# Trait System Implementation Plan (Phase 2)

**Date:** 2026-02-03
**Priority:** P2 (High Value)
**Estimated Effort:** 30 hours
**Status:** Planning Phase
**Dependencies:** Type Inference (✅ Complete)

---

## Overview

Implement Rust-style traits for Simple, enabling:
- Generic bounds (`fn sort<T: Ord>`)
- Trait implementations (`impl Display for Point`)
- Trait objects (`dyn Trait`)
- Method resolution with traits
- Default trait methods

**Goal:** Match Rust's trait system capabilities for generic programming.

---

## Current Limitations

Simple currently has **no trait resolution**:

```simple
# ❌ Cannot express:
fn sort<T: Ord>(list: [T]) -> [T]     # Where clause unsupported
impl ToString for Point                # No trait impls
val x: dyn Display                     # No dynamic dispatch
trait Iterator:
    type Item                          # No associated types
```

**Problems:**
- Cannot constrain generic types
- Cannot define shared interfaces
- Cannot do polymorphic dispatch
- Cannot express type relationships

---

## Design

### Trait System Architecture

```
TraitDef (definition)
    ↓ requires
ImplBlock (implementation)
    ↓ generates
Obligation (T: Trait)
    ↓ solved by
TraitSolver (find matching impl)
    ↓ enables
Method Resolution (dispatch)
```

### Core Types

```simple
class TraitDef:
    """Trait definition"""
    name: Symbol
    type_params: [TypeParam]
    supertraits: [TraitRef]
    methods: [MethodSig]
    assoc_types: [AssocTypeDef]

class ImplBlock:
    """Trait implementation"""
    trait_ref: TraitRef           # Which trait
    for_type: HirType             # For which type
    where_clause: [TraitBound]    # Conditions
    methods: [HirFunction]        # Method definitions
    assoc_types: [AssocTypeBinding]

class Obligation:
    """Type must satisfy trait"""
    ty: HirType                   # T
    trait_ref: TraitRef           # Ord
    span: Span                    # For errors

class TraitSolver:
    """Finds matching impl blocks"""
    trait_defs: Dict<Symbol, TraitDef>
    impl_blocks: [ImplBlock]

    fn solve(obligation: Obligation) -> Result<ImplBlock>
```

---

## Implementation Phases

### Phase 2A: Trait Definitions (8 hours)

**Goal:** Parse and store trait definitions

#### Tasks

1. **AST Extension (2h)**
   ```simple
   # New AST nodes
   trait Display:
       fn to_string() -> text

   trait Iterator:
       type Item
       fn next() -> Item?
   ```

2. **TraitDef Storage (3h)**
   - Create `TraitRegistry` class
   - Store trait definitions by name
   - Validate trait syntax (no duplicate methods)
   - Check supertrait cycles

3. **Method Signatures (2h)**
   - Parse method signatures
   - Store parameter types and return types
   - Handle `self` parameter types

4. **Testing (1h)**
   - Define builtin traits (Display, Ord, Eq)
   - Test trait definition parsing
   - Test method signature storage

**Deliverable:** `src/compiler/trait_def.spl` (200 lines)

---

### Phase 2B: Impl Blocks (8 hours)

**Goal:** Parse and store trait implementations

#### Tasks

1. **Impl Block Parsing (3h)**
   ```simple
   impl Display for Point:
       fn to_string() -> text:
           "Point({self.x}, {self.y})"

   impl<T: Display> Display for Option<T>:
       fn to_string() -> text:
           match self:
               Some(v): "Some({v})"
               None: "None"
   ```

2. **ImplBlock Storage (3h)**
   - Create `ImplRegistry` class
   - Index impls by (trait, type) pairs
   - Validate impl completeness (all methods defined)
   - Check method signatures match trait

3. **Orphan Rule (1h)**
   - Impl must be in trait's crate OR type's crate
   - Prevent conflicting impls

4. **Testing (1h)**
   - Test simple impls (Display for Point)
   - Test generic impls (Display for Option<T>)
   - Test orphan rule violations

**Deliverable:** `src/compiler/trait_impl.spl` (250 lines)

---

### Phase 2C: Obligation Solver (10 hours)

**Goal:** Solve trait bounds and find matching impls

#### Tasks

1. **Obligation Collection (3h)**
   ```simple
   fn sort<T: Ord>(list: [T]):
       # Generates obligation: T: Ord
       list[0] < list[1]  # Uses Ord::lt method
   ```

   - Collect trait bounds from function signatures
   - Collect bounds from where clauses
   - Collect bounds from method calls

2. **Impl Matching (4h)**
   ```simple
   # Given: obligation T: Display
   # Search: impl Display for T

   fn match_impl(obligation: Obligation) -> ImplBlock?:
       for impl_block in registry.impls:
           if impl_block.trait == obligation.trait:
               if unify(impl_block.for_type, obligation.ty):
                   return Some(impl_block)
       None
   ```

3. **Recursive Obligations (2h)**
   ```simple
   impl<T: Display> Display for Vec<T>:
       # Requires: T: Display (recursive)
   ```

   - Handle nested trait bounds
   - Fixed-point iteration for transitive bounds

4. **Testing (1h)**
   - Test direct impl matching (i32: Ord)
   - Test generic impl matching (Vec<i32>: Display)
   - Test recursive obligations

**Deliverable:** `src/compiler/trait_solver.spl` (300 lines)

---

### Phase 2D: Method Resolution (4 hours)

**Goal:** Resolve method calls using trait information

#### Tasks

1. **Method Lookup (2h)**
   ```simple
   val x: i32 = 42
   x.to_string()  # Lookup: i32 has Display? → Find impl Display for i32
   ```

   - Search inherent methods (defined on type)
   - Search trait methods (via impl blocks)
   - Prioritize inherent over trait

2. **Disambiguation (1h)**
   ```simple
   # Multiple traits with same method name
   Trait1::method(x)  # Explicit trait qualification
   ```

3. **Testing (1h)**
   - Test method resolution
   - Test disambiguation

**Deliverable:** Add to `src/compiler/trait_solver.spl` (+100 lines)

---

### Phase 2E: Trait Objects (5 hours) - OPTIONAL

**Goal:** Dynamic dispatch with `dyn Trait`

#### Tasks

1. **Trait Object Types (2h)**
   ```simple
   val x: dyn Display = Point(1, 2)
   x.to_string()  # Virtual call
   ```

2. **Vtable Generation (2h)**
   - Generate vtable for each (type, trait) pair
   - Store function pointers

3. **Testing (1h)**
   - Test trait object creation
   - Test method calls through trait objects

**Deliverable:** `src/compiler/trait_objects.spl` (200 lines)

---

### Phase 2F: Associated Types (3 hours) - OPTIONAL

**Goal:** Type projections in traits

#### Tasks

1. **Associated Type Definitions (1h)**
   ```simple
   trait Iterator:
       type Item
       fn next() -> Item?
   ```

2. **Associated Type Bindings (1h)**
   ```simple
   impl Iterator for Range:
       type Item = i32
   ```

3. **Type Projection (1h)**
   ```simple
   fn process<I: Iterator>(iter: I) where I::Item: Display
   ```

**Deliverable:** Add to `src/compiler/trait_def.spl` (+150 lines)

---

### Phase 2G: Default Methods (2 hours) - OPTIONAL

**Goal:** Provide default implementations

```simple
trait Iterator:
    fn next() -> Item?

    # Default method (can be overridden)
    fn count() -> i64:
        var n = 0
        while self.next().is_some():
            n = n + 1
        n
```

**Deliverable:** Add to `src/compiler/trait_def.spl` (+100 lines)

---

## Implementation Order

### Core (Required - 30 hours)

1. **Phase 2A:** Trait Definitions (8h)
2. **Phase 2B:** Impl Blocks (8h)
3. **Phase 2C:** Obligation Solver (10h)
4. **Phase 2D:** Method Resolution (4h)

### Extensions (Optional - 10 hours)

5. **Phase 2E:** Trait Objects (5h)
6. **Phase 2F:** Associated Types (3h)
7. **Phase 2G:** Default Methods (2h)

**Total:** 30h core + 10h optional = 40h full implementation

---

## Test Strategy

### Unit Tests (Per Phase)

| Phase | Tests | Coverage |
|-------|-------|----------|
| 2A | 10 | Trait definition parsing |
| 2B | 12 | Impl block parsing + validation |
| 2C | 15 | Obligation solving |
| 2D | 8 | Method resolution |
| **Total** | **45** | **All core features** |

### Integration Tests

```simple
# Test 1: Basic trait usage
trait Display:
    fn to_string() -> text

impl Display for i32:
    fn to_string() -> text:
        "{self}"

fn print_display<T: Display>(x: T):
    print x.to_string()

print_display(42)  # Should print "42"

# Test 2: Generic constraints
fn sort<T: Ord>(list: [T]) -> [T]:
    # ... uses T::lt ...

sort([3, 1, 2])  # Should work (i32: Ord)

# Test 3: Trait objects (optional)
val displayable: dyn Display = 42
print displayable.to_string()
```

---

## Built-in Traits

Define these standard traits:

```simple
trait Eq:
    fn eq(other: Self) -> bool

trait Ord: Eq:
    fn lt(other: Self) -> bool
    fn le(other: Self) -> bool
    fn gt(other: Self) -> bool
    fn ge(other: Self) -> bool

trait Display:
    fn to_string() -> text

trait Debug:
    fn debug() -> text

trait Clone:
    fn clone() -> Self

trait Copy: Clone  # Marker trait

trait Default:
    fn default() -> Self

trait Iterator:
    type Item
    fn next() -> Item?

trait FromStr:
    fn from_str(s: text) -> Self?
```

**Implementation:** `src/lib/traits/mod.spl` (200 lines)

---

## File Structure

```
src/compiler/
├── trait_def.spl           (200 lines)  - TraitDef, TraitRegistry
├── trait_impl.spl          (250 lines)  - ImplBlock, ImplRegistry
├── trait_solver.spl        (400 lines)  - Obligation, TraitSolver, method resolution
├── trait_objects.spl       (200 lines)  - Optional: dyn Trait
└── trait_validation.spl    (150 lines)  - Coherence, orphan rule

src/lib/traits/
└── mod.spl                 (200 lines)  - Built-in trait definitions

Total: ~1,400 lines of implementation
```

---

## Integration Points

### With Type Inference

```
Type Inference:
    1. Collect trait bounds from signatures
    2. Generate obligations
    3. Call TraitSolver.solve(obligation)
    4. If no impl found → type error
```

### With Method Resolution

```
Method Call:
    1. Look up inherent methods (on type itself)
    2. Look up trait methods (search impl blocks)
    3. If ambiguous → require explicit trait qualification
```

### With Codegen

```
Codegen:
    - Static dispatch: inline method call
    - Dynamic dispatch: virtual call through vtable
```

---

## Error Messages

### Missing Trait Impl

```
error[E0277]: the trait bound `Point: Display` is not satisfied
  --> example.spl:10:5
   |
10 |     print_display(p)
   |     ^^^^^^^^^^^^^ the trait `Display` is not implemented for `Point`
   |
help: consider implementing `Display` for `Point`
   |
   | impl Display for Point:
   |     fn to_string() -> text:
   |         # ...
```

### Method Not Found

```
error[E0599]: no method named `to_string` found for type `Point`
  --> example.spl:5:7
   |
5  |     p.to_string()
   |       ^^^^^^^^^ method not found in `Point`
   |
help: items from traits can only be used if the trait is in scope
   |
   | use std.traits.Display
```

---

## Performance Considerations

### Time Complexity

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Trait lookup | O(1) | HashMap by name |
| Impl lookup | O(n) | Linear search (can optimize with indexing) |
| Obligation solving | O(k × m) | k = obligations, m = impls |
| Method resolution | O(n) | n = number of impls |

### Optimizations

1. **Impl Indexing** - Index by (trait, type) for O(1) lookup
2. **Caching** - Cache solved obligations
3. **Early Exit** - Stop on first matching impl
4. **Specialization** - Prefer more specific impls

---

## Timeline

### Week 1: Core Infrastructure (16h)

- Day 1-2: Phase 2A (Trait Definitions)
- Day 3-4: Phase 2B (Impl Blocks)

### Week 2: Solver & Resolution (14h)

- Day 1-2: Phase 2C (Obligation Solver)
- Day 3: Phase 2D (Method Resolution)

**Total: 30 hours over 2 weeks**

---

## Success Criteria

✅ Trait system is complete when:

1. **Functionality**
   - Can define traits with methods
   - Can implement traits for types
   - Can constrain generics with trait bounds
   - Can resolve methods through traits
   - Obligation solver finds matching impls

2. **Testing**
   - 45+ unit tests passing
   - Integration tests demonstrate real usage
   - Built-in traits defined and working

3. **Error Messages**
   - Clear "trait not implemented" errors
   - Helpful suggestions for fixing

4. **Performance**
   - Obligation solving < 1ms typical
   - Method resolution < 100μs per call

---

## Risks & Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Complex obligation solving | High | High | Start with simple cases, iterate |
| Method resolution ambiguity | Medium | Medium | Implement disambiguation early |
| Coherence checking | Medium | High | Defer to Phase 2B, simple rules first |
| Performance issues | Low | Medium | Profile early, optimize hot paths |

---

## Future Extensions (Out of Scope)

After Phase 2 complete:

1. **Specialization (15h)** - Prefer more specific impls
2. **Higher-Kinded Types (20h)** - Traits over type constructors
3. **Auto Traits (8h)** - Send, Sync markers
4. **Negative Impls (6h)** - `impl !Trait for Type`
5. **Impl Trait (10h)** - `fn f() -> impl Trait`

**Total Future Work:** 59 hours (optional)

---

## References

### Rust Implementation

- `rustc_trait_selection` - Trait solver
- `rustc_typeck` - Trait checking
- Chalk solver - Advanced trait resolution

### Theory

- Hindley-Milner with type classes
- Haskell's type class system
- Scala's implicit resolution

---

**Status:** Ready to implement
**Next Step:** Phase 2A - Trait Definitions (8h)
**Estimated Completion:** 2026-02-10 (7 days from now)
