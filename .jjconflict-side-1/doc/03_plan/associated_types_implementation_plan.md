# Associated Types Implementation Plan

**Phase:** 4 (Rust Feature Parity Roadmap)
**Estimated Time:** 8 hours
**Status:** 🚧 In Progress
**Dependencies:** Phase 2 (Trait System) ✅ Complete

---

## Overview

Associated types allow traits to define type members that implementing types must specify. This is crucial for:
- Generic container traits (Iterator, Collection)
- Type-level computation
- Cleaner trait bounds (no extra type parameters)
- GATs (Generic Associated Types) preparation

**Key Difference from Type Parameters:**

```simple
# Without associated types (verbose):
trait Iterator<Item>:
    fn next() -> Item?

fn sum<I, T>(iter: I) -> T
    where I: Iterator<T>:
    # Need both I and T as parameters

# With associated types (clean):
trait Iterator:
    type Item  # Associated type

    fn next() -> Item?

fn sum<I>(iter: I) -> I.Item
    where I: Iterator:
    # Only need I, Item is accessed via I.Item
```

---

## Architecture

### New Components

```
src/compiler/
├── trait_def.spl              # ✅ Exists (extend)
├── trait_impl.spl             # ✅ Exists (extend)
├── trait_solver.spl           # ✅ Exists (extend)
├── trait_method_resolution.spl # ✅ Exists (extend)
└── associated_types.spl       # 🆕 NEW (Phase 4)
```

### Data Structures

```simple
# In trait_def.spl - extend TraitDef
class AssocTypeDef:
    name: Symbol
    bounds: [TraitRef]  # Optional bounds: type Item: Display
    default: HirType?    # Optional default type

class TraitDef:
    # ... existing fields ...
    assoc_types: Dict<Symbol, AssocTypeDef>  # NEW

# In trait_impl.spl - extend ImplBlock
class AssocTypeImpl:
    name: Symbol
    concrete_type: HirType

class ImplBlock:
    # ... existing fields ...
    assoc_type_impls: Dict<Symbol, AssocTypeImpl>  # NEW

# In associated_types.spl - NEW
class AssocTypeProjection:
    """
    Type projection: T.Item where T: Iterator

    Example: I.Item in fn sum<I: Iterator>(iter: I) -> I.Item
    """
    base_type: HirType     # I
    assoc_name: Symbol     # Item
    resolved: HirType?     # Cached resolution

class AssocTypeResolver:
    """
    Resolves associated type projections
    """
    impl_registry: ImplRegistry
    trait_registry: TraitRegistry

    fn resolve_projection(projection: AssocTypeProjection) -> HirType
    fn normalize(ty: HirType) -> HirType
```

---

## Implementation Phases

### Phase 4A: Associated Type Definitions (2 hours)

**File:** Extend `src/compiler/trait_def.spl`

**Tasks:**
1. Add `AssocTypeDef` class
   - name, bounds, default fields
   - `to_string()` method
2. Extend `TraitDef` to include `assoc_types: Dict<Symbol, AssocTypeDef>`
3. Add methods:
   - `me add_assoc_type(assoc_type: AssocTypeDef)`
   - `fn has_assoc_type(name: Symbol) -> bool`
   - `fn get_assoc_type(name: Symbol) -> AssocTypeDef?`
   - `fn assoc_type_count() -> i64`
4. Update built-in traits:
   ```simple
   # Iterator trait
   val iterator = TraitDef.new("Iterator")
   val item_type = AssocTypeDef.new("Item")
   iterator.add_assoc_type(item_type)
   ```

**Tests:**
- Basic associated type definition
- Trait with multiple associated types
- Associated type with bounds
- Default associated type

---

### Phase 4B: Associated Type Implementations (2 hours)

**File:** Extend `src/compiler/trait_impl.spl`

**Tasks:**
1. Add `AssocTypeImpl` class
   - name, concrete_type fields
2. Extend `ImplBlock` to include `assoc_type_impls: Dict<Symbol, AssocTypeImpl>`
3. Add methods:
   - `me add_assoc_type_impl(name: Symbol, concrete_type: HirType)`
   - `fn get_assoc_type_impl(name: Symbol) -> HirType?`
   - `fn has_assoc_type_impl(name: Symbol) -> bool`
4. Update validation to check:
   - All required associated types are implemented
   - Associated type impls satisfy trait bounds
5. Update built-in impls:
   ```simple
   # impl Iterator for Range
   val range_iter = ImplBlock.new(TraitRef.new("Iterator"), HirType.Named("Range"))
   range_iter.add_assoc_type_impl("Item", HirType.Int)
   ```

**Tests:**
- Basic associated type impl
- Multiple associated types
- Missing associated type (error)
- Associated type bound satisfaction
- Default associated type usage

---

### Phase 4C: Type Projection & Resolution (3 hours)

**File:** NEW `src/compiler/associated_types.spl`

**Tasks:**
1. Add `AssocTypeProjection` class
   - Represents `T.Item` syntax
   - base_type, assoc_name, cached resolution
2. Add `AssocTypeResolver` class with methods:
   - `fn resolve_projection(projection: AssocTypeProjection) -> HirType`
   - `fn normalize(ty: HirType) -> HirType`
   - `fn find_impl_for_projection(projection: AssocTypeProjection) -> ImplBlock?`
3. Implement resolution algorithm:
   ```simple
   fn resolve_projection(projection: AssocTypeProjection) -> HirType:
       # 1. Find impl for base type
       val base_type_name = projection.base_type.type_name()

       for impl_block in self.impl_registry.impls:
           if impl_block.for_type.matches(projection.base_type):
               # 2. Get associated type impl
               if impl_block.has_assoc_type_impl(projection.assoc_name):
                   return impl_block.get_assoc_type_impl(projection.assoc_name)

       # 3. Check for default
       # 4. Error if not found
       HirType.Error
   ```
4. Add normalization (reduce projections to concrete types):
   ```simple
   fn normalize(ty: HirType) -> HirType:
       match ty:
           case Projection(proj):
               self.resolve_projection(proj)
           case Generic(name, args):
               val normalized_args = args.map(self.normalize)
               HirType.Generic(name, normalized_args)
           case _:
               ty
   ```

**Tests:**
- Basic projection resolution
- Nested projections (`T.Assoc1.Assoc2`)
- Projection with generic base type
- Projection normalization
- Projection with default type
- Projection error (missing impl)

---

### Phase 4D: Integration & Bounds (1 hour)

**Files:** Update `trait_solver.spl`, `trait_method_resolution.spl`

**Tasks:**
1. Extend `Obligation` to handle associated type bounds:
   ```simple
   class Obligation:
       # ... existing fields ...
       assoc_type_constraints: Dict<Symbol, HirType>  # NEW
   ```
2. Update `TraitSolver.solve()` to check associated type constraints:
   ```simple
   fn solve(obligation: Obligation) -> bool:
       # ... existing impl matching ...

       # Check associated type constraints
       for (assoc_name, expected_type) in obligation.assoc_type_constraints:
           val actual_type = impl_block.get_assoc_type_impl(assoc_name)
           if not actual_type.matches(expected_type):
               return false

       true
   ```
3. Update method resolution to handle associated types in signatures
4. Add tests for:
   - Generic function with associated type in return
   - Trait bound with associated type constraint
   - Method using associated type

---

## Examples

### Example 1: Iterator Trait

```simple
# Trait definition
trait Iterator:
    type Item  # Associated type

    fn next() -> Item?
    fn collect() -> [Item]

# Implementation
impl Iterator for Range:
    type Item = i64  # Specify associated type

    fn next() -> i64?:
        if self.current <= self.end:
            val result = self.current
            self.current = self.current + 1
            Some(result)
        else:
            None

    fn collect() -> [i64]:
        var items = []
        while val Some(item) = self.next():
            items.push(item)
        items

# Usage
fn sum<I>(iter: I) -> I.Item
    where I: Iterator, I.Item: Add:
    var total = 0
    while val Some(item) = iter.next():
        total = total + item
    total

val range = Range(start: 1, end: 10)
val result = sum(range)  # I.Item resolves to i64
```

### Example 2: Collection Trait

```simple
trait Collection:
    type Item

    fn add(item: Item)
    fn remove(item: Item) -> bool
    fn contains(item: Item) -> bool

impl Collection for Vec:
    type Item = T  # Generic associated type

    fn add(item: T):
        self.items.push(item)

    fn remove(item: T) -> bool:
        # Implementation

    fn contains(item: T) -> bool:
        # Implementation
```

### Example 3: Associated Type Bounds

```simple
trait Graph:
    type Node: Display  # Bound: Node must implement Display
    type Edge: Display

    fn nodes() -> [Node]
    fn edges() -> [Edge]

impl Graph for SimpleGraph:
    type Node = i64      # i64 implements Display ✓
    type Edge = (i64, i64)  # tuple implements Display ✓

    # ... methods ...
```

### Example 4: Default Associated Type

```simple
trait Container:
    type Item
    type Index = i64  # Default type

    fn get(index: Index) -> Item?
    fn set(index: Index, value: Item)

impl Container for Array:
    type Item = T
    # Uses default Index = i64

    fn get(index: i64) -> T?:
        # Implementation

    fn set(index: i64, value: T):
        # Implementation
```

---

## Type System Extensions

### HirType Extensions

```simple
enum HirType:
    # ... existing variants ...
    Projection(base: HirType, assoc_name: Symbol)  # NEW: T.Item
    Error  # NEW: For unresolved projections

impl HirType:
    fn to_string() -> text:
        match self:
            # ... existing cases ...
            case Projection(base, name):
                "{base.to_string()}.{name}"
            case Error:
                "<error>"

    fn normalize(resolver: AssocTypeResolver) -> HirType:
        """Reduce projections to concrete types"""
        resolver.normalize(self)
```

---

## Validation Rules

### ImplBlock Validation

1. **Completeness:** All non-default associated types must be specified
2. **Bound Satisfaction:** Associated type impls must satisfy trait bounds
3. **Consistency:** Same associated type cannot be specified twice
4. **Default Override:** Can override default associated types

### Projection Validation

1. **Base Type Bound:** Base type must implement the trait
2. **Assoc Name Exists:** Associated type must exist in trait
3. **Resolvable:** Must find matching impl to resolve projection

---

## Error Handling

### Error Types

```simple
enum AssocTypeError:
    MissingAssocType(trait_name: Symbol, assoc_name: Symbol)
    UnresolvedProjection(base: HirType, assoc_name: Symbol)
    BoundUnsatisfied(assoc_name: Symbol, expected: TraitRef, actual: HirType)
    DuplicateAssocType(name: Symbol)
    DefaultOverrideInvalid(name: Symbol)
```

### Error Messages

```simple
# Missing associated type
"error: missing associated type `Item` in impl of `Iterator` for `Range`"

# Unresolved projection
"error: cannot resolve `T.Item`: no impl of `Iterator` found for `T`"

# Bound unsatisfied
"error: associated type `Node` does not satisfy bound `Display`
  --> graph.spl:42:5
   |
42 |     type Node = PrivateType
   |     ^^^^^^^^^^^^^^^^^^^^^^^ does not implement `Display`"
```

---

## Testing Strategy

### Unit Tests (20+ tests)

**Phase 4A Tests (5 tests):**
- `test_assoc_type_basic()` - Define trait with associated type
- `test_multiple_assoc_types()` - Multiple associated types in one trait
- `test_assoc_type_with_bounds()` - Associated type with trait bounds
- `test_default_assoc_type()` - Default associated type
- `test_builtin_iterator_trait()` - Built-in Iterator trait

**Phase 4B Tests (6 tests):**
- `test_assoc_type_impl_basic()` - Implement associated type
- `test_multiple_assoc_type_impls()` - Multiple associated types in impl
- `test_missing_assoc_type()` - Error when not specified
- `test_assoc_type_bound_satisfied()` - Bound checking
- `test_default_assoc_type_usage()` - Using default
- `test_builtin_range_iterator()` - Built-in Range iterator impl

**Phase 4C Tests (7 tests):**
- `test_projection_basic()` - Resolve `T.Item`
- `test_nested_projection()` - Resolve `T.Assoc1.Assoc2`
- `test_projection_with_generic()` - Generic base type
- `test_projection_normalization()` - Normalize complex types
- `test_projection_default()` - Projection with default
- `test_projection_error()` - Missing impl error
- `test_projection_caching()` - Cache resolution results

**Phase 4D Tests (3 tests):**
- `test_generic_with_assoc_return()` - Function returning `I.Item`
- `test_trait_bound_with_assoc_constraint()` - `I: Iterator<Item=i64>`
- `test_method_with_assoc_type()` - Method using associated types

---

## Performance Considerations

| Operation | Complexity | Optimization |
|-----------|-----------|--------------|
| Projection resolution | O(I) | Cache results |
| Type normalization | O(depth) | Memoization |
| Bound checking | O(B × I) | Early exit |
| Impl lookup | O(1) | Indexed registry |

**Key Optimizations:**
- Cache projection resolutions in `AssocTypeProjection.resolved`
- Normalize types eagerly during type checking
- Use structural sharing for complex normalized types

---

## Integration Points

### Type Checker

```simple
# In type_checker.spl
fn check_generic_call(generic_func: HirFunction, type_args: [HirType]):
    # Substitute type parameters
    var subst = {}
    for (param, arg) in zip(generic_func.type_params, type_args):
        subst[param] = arg

    # Resolve associated types in substitution
    for (param, ty) in subst:
        subst[param] = assoc_type_resolver.normalize(ty)

    # Check bounds with normalized types
    for bound in generic_func.bounds:
        val normalized_ty = subst[bound.type_param]
        check_bound(normalized_ty, bound)
```

### HIR Lowering

```simple
# In hir_lowering.spl
fn lower_type(ast_type: AstType) -> HirType:
    match ast_type:
        case Projection(base, assoc_name):
            val base_hir = lower_type(base)
            HirType.Projection(base: base_hir, assoc_name: assoc_name)
        # ... other cases ...
```

---

## Future Extensions

### GATs (Generic Associated Types) - Phase 4.5

```simple
trait Collection:
    type Iter<'a>: Iterator<Item=&'a Self.Item>  # GAT with lifetime

    fn iter<'a>() -> Iter<'a>
```

### Associated Constants

```simple
trait Array:
    type Item
    const SIZE: i64  # Associated constant

    fn get(index: i64) -> Item?
```

---

## Success Criteria

✅ **Phase 4A Complete:**
- AssocTypeDef class implemented
- TraitDef extended with associated types
- Built-in Iterator trait defined
- 5 tests passing

✅ **Phase 4B Complete:**
- AssocTypeImpl class implemented
- ImplBlock extended with associated type impls
- Validation for completeness and bounds
- 6 tests passing

✅ **Phase 4C Complete:**
- AssocTypeProjection and resolver implemented
- Projection resolution working
- Type normalization working
- 7 tests passing

✅ **Phase 4D Complete:**
- TraitSolver handles associated type constraints
- Method resolution works with associated types
- 3 tests passing

✅ **Overall Success:**
- All 21+ tests passing
- Zero compiler errors
- Examples compile and run
- Ready for compiler integration

---

## Timeline

| Phase | Duration | Cumulative |
|-------|----------|-----------|
| 4A: Definitions | 2h | 2h |
| 4B: Implementations | 2h | 4h |
| 4C: Projection & Resolution | 3h | 7h |
| 4D: Integration | 1h | 8h |

**Total: 8 hours**

---

## References

**Completed Phases:**
- Phase 2: Trait System ✅
- Phase 3: Effect System ✅

**Related Documentation:**
- Rust RFC 195: Associated Items
- Rust RFC 1598: Generic Associated Types
- Type Theory: Type Families and Type Operators

---

**Status:** 🚧 Ready to Start Phase 4A
**Next Step:** Implement AssocTypeDef and extend TraitDef
