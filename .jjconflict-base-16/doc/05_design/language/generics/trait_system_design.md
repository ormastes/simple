# Trait System Design for Simple

**Date:** 2026-02-03
**Status:** Design Phase
**Estimated Effort:** 30 hours
**Implementation Target:** `src/compiler/traits.spl`

---

## Overview

Implement Rust-style traits for Simple, enabling:
- Generic bounds: `fn sort<T: Ord>(list: [T])`
- Polymorphic code with trait constraints
- Dynamic dispatch: `dyn Trait`
- Default method implementations
- Associated types (Phase 4)

---

## Core Concepts

### 1. Traits

**Definition:** Interface declaring methods that types can implement
```simple
trait Display:
    fn to_string() -> text

trait Iterator:
    type Item  # Associated type (Phase 4)
    fn next() -> Item?
```

### 2. Impl Blocks

**Definition:** Implementation of a trait for a specific type
```simple
impl Display for Point:
    fn to_string() -> text:
        "Point({self.x}, {self.y})"
```

### 3. Trait Bounds

**Definition:** Constraints on generic type parameters
```simple
fn print_all<T: Display>(items: [T]):
    for item in items:
        print item.to_string()
```

### 4. Trait Objects

**Definition:** Dynamic dispatch via trait pointers
```simple
val shapes: [dyn Shape] = [Circle(...), Rectangle(...)]
for shape in shapes:
    shape.draw()  # Dynamic dispatch
```

---

## Syntax

### Trait Declaration

```simple
trait TraitName:
    # Method signatures (no body)
    fn method_name(param: Type) -> ReturnType

    # Default implementations
    fn default_method():
        # implementation
```

**Example:**
```simple
trait Eq:
    fn eq(other: Self) -> bool
    fn ne(other: Self) -> bool:
        not self.eq(other)  # Default implementation
```

### Impl Block

```simple
impl TraitName for TypeName:
    fn method_name(param: Type) -> ReturnType:
        # implementation
```

**Example:**
```simple
impl Eq for Point:
    fn eq(other: Point) -> bool:
        self.x == other.x and self.y == other.y
```

### Generic Bounds

```simple
fn function_name<T: Trait1 + Trait2>(param: T) -> ReturnType:
    # body

# Multiple bounds
fn compare<T: Eq + Ord>(a: T, b: T) -> Ordering:
    if a < b: Less
    elif a > b: Greater
    else: Equal
```

### Trait Objects

```simple
# Trait object type
val obj: dyn Trait = concrete_value

# Array of trait objects
val items: [dyn Display] = [Point(...), Circle(...), "hello"]
```

---

## Type Definitions

### File: `src/compiler/traits.spl`

```simple
use compiler.hir.*
use compiler.lexer.*

# ============================================================================
# Trait Definition
# ============================================================================

struct TraitDef:
    """Definition of a trait.

    Traits declare method signatures that types can implement.
    """
    name: Symbol                    # Trait name
    methods: [MethodSignature]      # Required methods
    defaults: [HirFunction]         # Default implementations
    supertraits: [Symbol]           # Trait: Supertrait bounds
    span: Span

struct MethodSignature:
    """Method signature in a trait."""
    name: text
    params: [HirType]
    return_type: HirType
    effects: [Effect]
    span: Span

# ============================================================================
# Impl Block
# ============================================================================

struct ImplBlock:
    """Implementation of a trait for a type.

    impl Trait for Type { methods }
    """
    trait_name: Symbol              # Which trait
    for_type: HirType               # Which type
    where_clause: [TraitBound]      # Where T: Trait constraints
    methods: [HirFunction]          # Method implementations
    span: Span

# ============================================================================
# Trait Bound
# ============================================================================

struct TraitBound:
    """A constraint on a type parameter: T: Trait"""
    type_param: Symbol              # Type variable (T)
    trait_name: Symbol              # Required trait
    span: Span

enum TraitBoundKind:
    """Kind of trait bound."""
    Single(Symbol)                  # T: Trait
    Multiple([Symbol])              # T: Trait1 + Trait2
    Higher(Symbol, [TraitBound])    # T: Trait<U: OtherTrait>

# ============================================================================
# Obligation
# ============================================================================

struct Obligation:
    """A trait bound that must be proven.

    Created during type checking when generic functions are called.
    Must be satisfied by searching impl blocks.
    """
    type_: HirType                  # The type (e.g., i32, Vec<T>)
    trait_: Symbol                  # The trait (e.g., Display, Clone)
    cause: ObligationCause          # Why this obligation exists
    span: Span

enum ObligationCause:
    """Why an obligation was created."""
    FunctionCall(Symbol)            # From calling fn<T: Trait>
    MethodCall(Symbol, text)        # From calling method
    TraitBound(Symbol)              # From where clause
    BuiltIn                         # From built-in constraint

# ============================================================================
# Trait Solver
# ============================================================================

class TraitSolver:
    """Solves trait obligations by searching impl blocks.

    Algorithm:
    1. Collect obligations from function signatures
    2. For each obligation T: Trait:
       - Search for impl Trait for T
       - Check where clauses recursively
       - Report error if no impl found
    3. Cache results to avoid duplicate work
    """
    # All known trait definitions
    traits: Dict<Symbol, TraitDef>
    # All known impl blocks
    impls: Dict<(Symbol, HirType), ImplBlock>
    # Cache of solved obligations
    cache: Dict<(HirType, Symbol), bool>
    # Current obligations to solve
    obligations: [Obligation]
    # Errors encountered
    errors: [TraitError]

impl TraitSolver:
    static fn new() -> TraitSolver:
        TraitSolver(
            traits: {},
            impls: {},
            cache: {},
            obligations: [],
            errors: []
        )

    me add_trait(trait_def: TraitDef):
        """Register a trait definition."""
        self.traits[trait_def.name] = trait_def

    me add_impl(impl_block: ImplBlock):
        """Register an impl block."""
        val key = (impl_block.trait_name, impl_block.for_type)
        self.impls[key] = impl_block

    me add_obligation(ty: HirType, trait_: Symbol, cause: ObligationCause, span: Span):
        """Add an obligation to solve."""
        val obligation = Obligation(
            type_: ty,
            trait_: trait_,
            cause: cause,
            span: span
        )
        self.obligations = self.obligations.push(obligation)

    me solve_obligations() -> Result<(), [TraitError]>:
        """Solve all pending obligations.

        Returns Ok if all obligations satisfied, Err with errors otherwise.
        """
        for obligation in self.obligations:
            match self.solve_obligation(obligation):
                case Err(err):
                    self.errors = self.errors.push(err)
                case _: pass

        if self.errors.is_empty():
            Ok(())
        else:
            Err(self.errors)

    me solve_obligation(obligation: Obligation) -> Result<(), TraitError>:
        """Solve a single obligation.

        Algorithm:
        1. Check cache
        2. Search for impl block
        3. Recursively check where clauses
        4. Cache result
        """
        val ty = obligation.type_
        val trait_ = obligation.trait_

        # Check cache
        val cache_key = (ty, trait_)
        if self.cache[cache_key].?:
            if self.cache[cache_key]:
                return Ok(())
            else:
                return Err(TraitError.Unsatisfied(obligation))

        # Search for impl
        match self.find_impl(ty, trait_):
            case Some(impl_block):
                # Check where clauses
                for bound in impl_block.where_clause:
                    match self.solve_trait_bound(bound):
                        case Err(e): return Err(e)
                        case _: pass

                # Cache success
                self.cache[cache_key] = true
                Ok(())

            case None:
                # No impl found
                self.cache[cache_key] = false
                Err(TraitError.Unsatisfied(obligation))

    fn find_impl(ty: HirType, trait_: Symbol) -> ImplBlock?:
        """Find impl block for type and trait."""
        val key = (trait_, ty)
        self.impls[key]

    me solve_trait_bound(bound: TraitBound) -> Result<(), TraitError>:
        """Solve a trait bound from where clause."""
        val ty = HirType(kind: HirTypeKind.TypeParam(bound.type_param, []), span: bound.span)
        val cause = ObligationCause.TraitBound(bound.type_param)
        self.add_obligation(ty, bound.trait_name, cause, bound.span)
        # Will be solved in next iteration
        Ok(())

# ============================================================================
# Trait Errors
# ============================================================================

enum TraitError:
    """Errors from trait resolution."""
    Unsatisfied(obligation: Obligation)
    Ambiguous(type_: HirType, trait_: Symbol, candidates: [ImplBlock])
    Overlapping(impl1: ImplBlock, impl2: ImplBlock)
    MissingMethod(trait_: Symbol, method: text, type_: HirType)
    CyclicBound(type_param: Symbol)

impl TraitError:
    fn message() -> text:
        match self:
            case Unsatisfied(obligation):
                "trait bound not satisfied: {obligation.type_} does not implement {obligation.trait_}"
            case Ambiguous(ty, trait_, candidates):
                "ambiguous trait impl: {candidates.len()} candidates for {ty}: {trait_}"
            case Overlapping(impl1, impl2):
                "overlapping impls: {impl1.for_type} and {impl2.for_type}"
            case MissingMethod(trait_, method, ty):
                "missing method '{method}' in impl {trait_} for {ty}"
            case CyclicBound(param):
                "cyclic trait bound: {param}"
```

---

## Implementation Plan

### Phase A: Infrastructure (8 hours)

#### Step 1: Create traits.spl (2h)
- Type definitions (TraitDef, ImplBlock, etc.)
- Empty TraitSolver class

#### Step 2: Extend HIR (2h)
**File:** `src/compiler/hir.spl`
- Add `TraitDef` to HIR
- Add `ImplBlock` to HIR
- Add trait bounds to function signatures
- Add `dyn Trait` type variant

#### Step 3: Parser Support (4h)
**File:** `src/compiler/parser.spl` (or Rust parser)
- Parse `trait Name { methods }`
- Parse `impl Trait for Type { methods }`
- Parse trait bounds: `<T: Trait>`
- Parse trait objects: `dyn Trait`

### Phase B: Trait Resolution (12 hours)

#### Step 4: Impl Block Tracking (3h)
- Collect all trait definitions during compilation
- Collect all impl blocks
- Build lookup tables

#### Step 5: Obligation Generation (4h)
- At function calls, generate obligations from bounds
- At method calls, generate obligations from receiver
- Track obligation causes for error messages

#### Step 6: Obligation Solver (5h)
- Implement find_impl() search
- Implement recursive where clause checking
- Implement caching
- Handle built-in traits (Clone, Copy, etc.)

### Phase C: Method Resolution (7 hours)

#### Step 7: Trait Method Lookup (3h)
- Given receiver type + method name, find trait
- Check impl block has method
- Return method signature

#### Step 8: Dynamic Dispatch (4h)
- Implement vtable generation for `dyn Trait`
- Virtual method calls
- Trait object construction

### Phase D: Testing (3 hours)

#### Step 9: Unit Tests (2h)
- Trait definition and parsing
- Impl block registration
- Obligation solving
- Method resolution

#### Step 10: Integration Tests (1h)
- Generic functions with bounds
- Trait objects
- Default methods
- Error cases

---

## Examples

### Example 1: Display Trait

```simple
# Define trait
trait Display:
    fn to_string() -> text

# Implement for Point
struct Point:
    x: i64
    y: i64

impl Display for Point:
    fn to_string() -> text:
        "Point({self.x}, {self.y})"

# Use with generic bound
fn print_all<T: Display>(items: [T]):
    for item in items:
        print item.to_string()

# Call
val points = [Point(x: 1, y: 2), Point(x: 3, y: 4)]
print_all(points)  # Works because Point: Display
```

### Example 2: Eq and Ord Traits

```simple
trait Eq:
    fn eq(other: Self) -> bool
    fn ne(other: Self) -> bool:
        not self.eq(other)

trait Ord: Eq:  # Supertrait: Ord requires Eq
    fn cmp(other: Self) -> Ordering

impl Eq for i64:
    fn eq(other: i64) -> bool:
        # Built-in implementation
        self == other

impl Ord for i64:
    fn cmp(other: i64) -> Ordering:
        if self < other: Less
        elif self > other: Greater
        else: Equal

fn max<T: Ord>(a: T, b: T) -> T:
    if a.cmp(b) == Greater: a else: b

val result = max(10, 20)  # Returns 20
```

### Example 3: Trait Objects

```simple
trait Shape:
    fn area() -> f64
    fn draw()

struct Circle:
    radius: f64

impl Shape for Circle:
    fn area() -> f64:
        3.14159 * self.radius * self.radius

    fn draw():
        print "Drawing circle with radius {self.radius}"

struct Rectangle:
    width: f64
    height: f64

impl Shape for Rectangle:
    fn area() -> f64:
        self.width * self.height

    fn draw():
        print "Drawing rectangle {self.width}x{self.height}"

# Heterogeneous array of shapes
val shapes: [dyn Shape] = [
    Circle(radius: 5.0),
    Rectangle(width: 10.0, height: 20.0)
]

for shape in shapes:
    shape.draw()          # Dynamic dispatch
    print shape.area()    # Dynamic dispatch
```

---

## Integration with Type Inference

### Modified Type Checking Flow

```simple
fn check_function_call(call: HirExpr, fn_sig: FunctionSignature):
    # 1. Infer argument types
    var arg_types: [HirType] = []
    for arg in call.args:
        arg_types.push(infer_expr(arg))

    # 2. Generate obligations from trait bounds
    for bound in fn_sig.bounds:
        trait_solver.add_obligation(
            bound.type_param,
            bound.trait_name,
            ObligationCause.FunctionCall(fn_sig.name),
            call.span
        )

    # 3. Solve obligations
    match trait_solver.solve_obligations():
        case Err(errors):
            for error in errors:
                report_error(error)
        case _: pass

    # 4. Return function return type
    fn_sig.return_type
```

---

## Coherence Rules

### Orphan Rule
**Rule:** Can only impl a trait for a type if:
- The trait is defined in the current crate, OR
- The type is defined in the current crate

**Example:**
```simple
# In crate A:
trait Display: ...

# In crate B:
struct Point: ...

# In crate C:
impl Display for Point:  # ❌ ERROR: Orphan impl
    # Neither Display nor Point defined in crate C
```

### No Overlapping Impls
**Rule:** Cannot have two impls that could match the same type

**Example:**
```simple
impl Display for i64: ...        # OK
impl Display for i64: ...        # ❌ ERROR: Duplicate impl

impl<T> Display for Vec<T>: ...  # OK
impl Display for Vec<i32>: ...   # ❌ ERROR: Overlaps with generic impl
```

---

## Built-in Traits

Simple provides several built-in traits:

```simple
trait Clone:
    fn clone() -> Self

trait Copy: Clone:  # Marker trait

trait Debug:
    fn debug() -> text

trait Default:
    fn default() -> Self

trait Drop:
    fn drop()

trait Eq:
    fn eq(other: Self) -> bool

trait Ord: Eq:
    fn cmp(other: Self) -> Ordering
```

---

## Performance Considerations

### Static Dispatch (Monomorphization)
**Default:** Generate specialized code for each concrete type
```simple
fn print_all<T: Display>(items: [T]):
    # Compiled separately for each T
```

**Result:**
- Fast: no runtime overhead
- Code size: duplicated for each type

### Dynamic Dispatch (Trait Objects)
**Opt-in:** Use `dyn Trait` for runtime polymorphism
```simple
val items: [dyn Display] = [...]
```

**Result:**
- Flexible: heterogeneous collections
- Overhead: vtable lookup (~1 cycle)

---

## Timeline

| Phase | Task | Hours | Cumulative |
|-------|------|-------|------------|
| A | Infrastructure | 8h | 8h |
| B | Trait Resolution | 12h | 20h |
| C | Method Resolution | 7h | 27h |
| D | Testing | 3h | 30h |

**Total: 30 hours (~1 week full-time)**

---

## Success Criteria

- ✅ Trait definitions parse and compile
- ✅ Impl blocks register correctly
- ✅ Generic functions with trait bounds work
- ✅ Obligation solver finds correct impls
- ✅ Method calls dispatch to correct impl
- ✅ Trait objects support dynamic dispatch
- ✅ Default methods inherit correctly
- ✅ Coherence rules enforced
- ✅ 50+ tests passing
- ✅ Real-world example (collections with traits)

---

## Next Steps

1. Create `src/compiler/traits.spl` with type definitions
2. Extend HIR to support traits
3. Implement trait solver
4. Add parser support (or coordinate with Rust parser)
5. Comprehensive testing

---

**Status:** Ready for Implementation
**Priority:** High (enables generic programming)
**Dependencies:** None (can start immediately)
