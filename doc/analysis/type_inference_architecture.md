# Type Inference Architecture Comparison

**Date:** 2026-02-03
**Phase:** 7 - Architecture Documentation
**Related:** `doc/plan/type_inference_comparison_plan.md`

## Executive Summary

**Architectural Complexity:** Rust has **modular, layered architecture** spanning 15+ modules, Simple has **monolithic single-file** implementation.

**Key Differences:**
- **Rust:** Multi-phase pipeline (Parse → HIR → Type Check → Codegen)
- **Simple:** Single-phase unification (no integration with compiler pipeline)

**Design Patterns:**
- **Rust:** Visitor, Builder, Strategy patterns
- **Simple:** Basic class with methods

---

## High-Level Architecture

### Rust Type Inference Pipeline

```
┌─────────────────────────────────────────────────────────────────┐
│                     RUST COMPILER PIPELINE                       │
└─────────────────────────────────────────────────────────────────┘

 Source Code (.spl)
      ↓
 ┌─────────────┐
 │   Lexer     │ → Tokens
 └─────────────┘
      ↓
 ┌─────────────┐
 │   Parser    │ → AST (with Spans)
 └─────────────┘
      ↓
 ┌─────────────────────────────────────────────────────────────┐
 │                  HIR (High-Level IR)                        │
 │                                                              │
 │  ┌──────────────────┐     ┌─────────────────┐             │
 │  │  AST Lowering    │ →   │  Type Registry  │             │
 │  │  - type_resolver │     │  - TypeId alloc │             │
 │  │  - inference.rs  │     │  - Named types  │             │
 │  └──────────────────┘     └─────────────────┘             │
 │           ↓                                                 │
 │  ┌──────────────────────────────────────────────────────┐  │
 │  │            Type Checking Phase                       │  │
 │  │  - checker_infer.rs  (expression inference)          │  │
 │  │  - checker_unify.rs  (unification)                   │  │
 │  │  - checker_check.rs  (validation)                    │  │
 │  │  - checker_builtins.rs (built-in types)             │  │
 │  └──────────────────────────────────────────────────────┘  │
 │           ↓                                                 │
 │  ┌──────────────────────────────────────────────────────┐  │
 │  │         Advanced Checking (optional)                 │  │
 │  │  - effects.rs         (async/effect tracking)        │  │
 │  │  - dispatch_checker.rs (dynamic traits)              │  │
 │  │  - macro_checker.rs   (macro expansion)              │  │
 │  │  - mixin_checker.rs   (mixin composition)            │  │
 │  └──────────────────────────────────────────────────────┘  │
 └─────────────────────────────────────────────────────────────┘
      ↓
 ┌─────────────────┐
 │ Monomorphization│ → Specialized HIR (generics resolved)
 └─────────────────┘
      ↓
 ┌─────────────────┐
 │    Codegen      │ → MIR → Machine Code / Bytecode
 └─────────────────┘
```

**Key Characteristics:**
- **Multi-stage:** Parse → HIR → Type Check → Codegen
- **Modular:** 15+ files, clear separation of concerns
- **Integrated:** Type checking embedded in compilation pipeline
- **Extensible:** Plugin architecture for advanced checkers

### Simple Type Inference (Standalone)

```
┌─────────────────────────────────────────────────────────────┐
│              SIMPLE TYPE INFERENCE MODULE                    │
│            (lib/std/src/type_checker/)                       │
└─────────────────────────────────────────────────────────────┘

 Input: Two types
      ↓
 ┌──────────────────────────────────────────────────┐
 │  type_inference_v3.spl (309 lines)              │
 │                                                   │
 │  ┌─────────────────┐                            │
 │  │  Type Enum      │  (8 variants)              │
 │  │  - Primitives   │                            │
 │  │  - Var(id)      │                            │
 │  │  - Function     │                            │
 │  │  - Generic      │                            │
 │  └─────────────────┘                            │
 │         ↓                                        │
 │  ┌─────────────────────────────┐                │
 │  │  TypeUnifier Class          │                │
 │  │  - substitution: Dict       │                │
 │  │  - next_var: i64            │                │
 │  │                              │                │
 │  │  Methods:                   │                │
 │  │  - fresh_var()              │                │
 │  │  - resolve(Type)            │                │
 │  │  - unify(Type, Type)        │                │
 │  │  - occurs_check(id, Type)   │                │
 │  └─────────────────────────────┘                │
 │         ↓                                        │
 │  ┌─────────────────────────────┐                │
 │  │  Test Suite (58 tests)      │                │
 │  │  - Built-in to module       │                │
 │  │  - Runs on load             │                │
 │  └─────────────────────────────┘                │
 └──────────────────────────────────────────────────┘
      ↓
 Output: bool (success/failure)
```

**Key Characteristics:**
- **Single-stage:** Just unification, no inference
- **Monolithic:** 1 file, everything in one place
- **Standalone:** Not integrated with compiler
- **Limited:** No expression inference, no environment

---

## Module Breakdown

### Rust Modules (15+ files, 2,358 lines)

#### Core Type Checking (4 modules, 1,820 lines)

| Module | Lines | Purpose | Key Functions |
|--------|-------|---------|---------------|
| **checker_infer.rs** | 310 | Expression inference | `infer_expr()` (20+ cases) |
| **checker_unify.rs** | 407 | Unification algorithm | `unify()`, `resolve()`, `ast_type_to_type()` |
| **checker_check.rs** | 711 | Type checking validation | `check_program()`, `check_stmt()` |
| **checker_builtins.rs** | 392 | Built-in type support | `register_builtins()`, primitive ops |

**Responsibilities:**
- Expression type inference (literals, operators, calls, etc.)
- Type unification (Robinson algorithm)
- Type validation (checks, constraints)
- Built-in type registration

#### HIR Lowering (3 modules, 538 lines)

| Module | Lines | Purpose | Key Functions |
|--------|-------|---------|---------------|
| **hir/lower/type_resolver.rs** | 353 | AST → TypeId | `resolve_type()`, `register_type()` |
| **hir/lower/type_registration.rs** | ~100 | Type collection | `collect_types()` |
| **hir/lower/expr/inference.rs** | 85 | Expression lowering | `lower_expr_with_inference()` |

**Responsibilities:**
- Convert AST types to internal TypeId representation
- Register named types (structs, classes, enums)
- Lower expressions while inferring types

#### Type System Infrastructure (2 modules, ~600 lines)

| Module | Lines | Purpose | Key Functions |
|--------|-------|---------|---------------|
| **hir/types/type_system.rs** | 391 | Type definitions | `Type` enum, constraints |
| **hir/type_registry.rs** | ~200 | TypeId management | `alloc_type()`, `get_type()` |

**Responsibilities:**
- Define Type enum and variants
- Allocate unique TypeIds
- Maintain type registry

#### Advanced Checkers (6 modules, ~1,200 lines)

| Module | Lines | Purpose |
|--------|-------|---------|
| **effects.rs** | ~200 | Async/effect tracking |
| **dispatch_checker.rs** | ~180 | Dynamic trait checking |
| **macro_checker.rs** | ~250 | Macro type validation |
| **mixin_checker.rs** | ~220 | Mixin composition |
| **bitfield.rs** | ~150 | Bitfield types |
| **tagged_union.rs** | ~200 | Union type support |

**Responsibilities:**
- Effect system (async/sync inference)
- Dynamic dispatch validation
- Macro hygiene and type checking
- Mixin trait composition
- Specialized type support

**Total:** 15+ modules, ~2,358 core lines + ~1,200 advanced = **3,558 lines**

### Simple Modules (1 file, 309 lines)

| File | Lines | Purpose |
|------|-------|---------|
| **type_inference_v3.spl** | 309 | Complete implementation |

**Breakdown:**
- Type enum definition: ~40 lines
- TypeUnifier class: ~90 lines
- Test suite: ~180 lines

**Total:** 1 file, 309 lines (12x smaller than Rust)

---

## Class Diagrams

### Rust Type Checker Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      TypeChecker                             │
├─────────────────────────────────────────────────────────────┤
│ Fields:                                                      │
│ - env: HashMap<String, Type>                                │
│ - subst: HashMap<usize, Type>                               │
│ - next_var: usize                                            │
│ - type_params: HashMap<String, Type>                         │
│ - available_macros: HashSet<String>                          │
│ - macros: HashMap<String, MacroDef>                          │
│ - fstring_keys: HashMap<String, Vec<String>>                │
├─────────────────────────────────────────────────────────────┤
│ Methods:                                                     │
│ + infer_expr(&Expr) -> Result<Type, TypeError>              │
│ + unify(&Type, &Type) -> Result<(), TypeError>              │
│ + resolve(&Type) -> Type                                     │
│ + fresh_var() -> Type                                        │
│ + check_program(&[Node]) -> Result<(), TypeError>           │
│ + ast_type_to_type(&AstType) -> Type                        │
│ + types_compatible(&Type, &Type) -> bool                    │
│ + check_match_arms(&[MatchArm]) -> Result<(), TypeError>    │
│ + get_fstring_keys_from_expr(&Expr) -> Option<Vec<String>>  │
│ + validate_dict_const_keys(&Expr, &Type) -> Result<(), ..>  │
└─────────────────────────────────────────────────────────────┘
              │
              │ uses
              ↓
┌─────────────────────────────────────────────────────────────┐
│                          Type                                │
├─────────────────────────────────────────────────────────────┤
│ Variants:                                                    │
│ - Int, Float, Bool, Str, Nil                                │
│ - Var(usize)                                                 │
│ - Named(String)                                              │
│ - Array(Box<Type>)                                           │
│ - Tuple(Vec<Type>)                                           │
│ - Function { params: Vec<Type>, ret: Box<Type> }            │
│ - Generic { name: String, args: Vec<Type> }                 │
│ - Optional(Box<Type>)                                        │
│ - Dict { key: Box<Type>, value: Box<Type> }                 │
│ - Union(Vec<Type>)                                           │
│ - Borrow(Box<Type>), BorrowMut(Box<Type>)                   │
│ - ConstKeySet { keys: Vec<String> }                         │
│ - DependentKeys { source: String }                          │
│ - DynTrait(String)                                           │
│ - ... (15+ variants total)                                   │
├─────────────────────────────────────────────────────────────┤
│ Methods:                                                     │
│ + apply_subst(&HashMap<usize, Type>) -> Type                │
│ + contains_var(usize) -> bool                               │
│ + display() -> String                                        │
└─────────────────────────────────────────────────────────────┘
              │
              │ produces
              ↓
┌─────────────────────────────────────────────────────────────┐
│                       TypeError                              │
├─────────────────────────────────────────────────────────────┤
│ Variants:                                                    │
│ - Undefined(String)                                          │
│ - Mismatch { expected: Type, found: Type }                  │
│ - OccursCheck { var_id: usize, ty: Type }                   │
│ - ArityMismatch { expected: usize, found: usize }           │
│ - Other(String)                                              │
├─────────────────────────────────────────────────────────────┤
│ Methods:                                                     │
│ + display() -> String                                        │
│ + suggestion() -> Option<String>                            │
└─────────────────────────────────────────────────────────────┘
```

### Simple Type Unifier Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      TypeUnifier                             │
├─────────────────────────────────────────────────────────────┤
│ Fields:                                                      │
│ - substitution: Dict<i64, Type>                             │
│ - next_var: i64                                              │
├─────────────────────────────────────────────────────────────┤
│ Methods:                                                     │
│ + fresh_var() -> Type                                        │
│ + resolve(Type) -> Type                                      │
│ + unify(Type, Type) -> bool                                  │
│ + occurs_check(i64, Type) -> bool                           │
└─────────────────────────────────────────────────────────────┘
              │
              │ uses
              ↓
┌─────────────────────────────────────────────────────────────┐
│                          Type                                │
├─────────────────────────────────────────────────────────────┤
│ Variants:                                                    │
│ - Int, Bool, Str, Float, Unit                               │
│ - Var(id: i64)                                               │
│ - Function(param_count: i64, return_id: i64)                │
│ - Generic(name: str, arg_count: i64)                        │
├─────────────────────────────────────────────────────────────┤
│ Methods:                                                     │
│ + to_string() -> str                                         │
│ + is_primitive() -> bool                                     │
└─────────────────────────────────────────────────────────────┘
              │
              │ produces
              ↓
┌─────────────────────────────────────────────────────────────┐
│                      Return Value                            │
├─────────────────────────────────────────────────────────────┤
│ Type: bool                                                   │
│ - true: success                                              │
│ - false: failure (no error info)                            │
└─────────────────────────────────────────────────────────────┘
```

**Comparison:**
- Rust: 3 classes (TypeChecker, Type, TypeError) + 15+ support modules
- Simple: 2 classes (TypeUnifier, Type) in 1 file

---

## Design Patterns

### Rust Design Patterns

#### 1. Visitor Pattern (Expression Inference)

```rust
impl TypeChecker {
    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Integer(_) => self.infer_integer(),
            Expr::Binary { left, right, op } => self.infer_binary(left, right, op),
            Expr::Call { callee, args } => self.infer_call(callee, args),
            // ... 20+ cases
        }
    }
}
```

**Benefits:**
- Extensible (add new expression types easily)
- Maintainable (each case isolated)
- Type-safe (exhaustiveness checking)

#### 2. Builder Pattern (Error Construction)

```rust
impl TypeError {
    pub fn mismatch(expected: Type, found: Type, span: Span) -> Self {
        TypeError::Mismatch { expected, found, span }
    }

    pub fn undefined(name: &str, span: Span) -> Self {
        TypeError::Undefined(name.to_string(), span)
    }
}

// Usage:
return Err(TypeError::mismatch(Type::Int, Type::Str, span));
```

**Benefits:**
- Consistent error construction
- Easy to add context (spans, notes)
- Fluent API

#### 3. Strategy Pattern (Type Resolution)

```rust
trait TypeResolver {
    fn resolve(&self, ty: &Type) -> Type;
}

struct SubstitutionResolver<'a> {
    subst: &'a HashMap<usize, Type>,
}

impl TypeResolver for SubstitutionResolver<'_> {
    fn resolve(&self, ty: &Type) -> Type {
        ty.apply_subst(self.subst)
    }
}
```

**Benefits:**
- Swappable resolution strategies
- Testable in isolation
- Composable

#### 4. Registry Pattern (Type Management)

```rust
pub struct TypeRegistry {
    types: Vec<Type>,
    names: HashMap<String, usize>,
}

impl TypeRegistry {
    pub fn alloc(&mut self, ty: Type) -> TypeId {
        let id = self.types.len();
        self.types.push(ty);
        TypeId(id)
    }

    pub fn get(&self, id: TypeId) -> &Type {
        &self.types[id.0]
    }
}
```

**Benefits:**
- Centralized type storage
- Efficient lookup (by ID)
- Prevents duplicates

### Simple Design Patterns

#### 1. Basic Class (No patterns)

```simple
class TypeUnifier:
    substitution: any
    next_var: i64

impl TypeUnifier:
    me fresh_var() -> Type: ...
    fn resolve(ty: Type) -> Type: ...
    me unify(t1: Type, t2: Type) -> bool: ...
```

**Characteristics:**
- Simple, straightforward
- No advanced patterns
- All logic in one class

**Trade-offs:**
- ✅ Easy to understand
- ❌ Not extensible
- ❌ Hard to test in isolation
- ❌ Coupling (all logic together)

---

## Data Flow Comparison

### Rust Type Checking Flow

```
Source Code
    ↓
Parser (simple-parser)
    ↓
AST with Spans
    ↓
┌───────────────────────────────────────────────────┐
│ HIR Lowering Phase                                │
│                                                    │
│ type_resolver.rs:                                 │
│ - Convert AST types to TypeId                     │
│ - Register named types in registry                │
│ - Build type environment                          │
│                                                    │
│ type_registration.rs:                             │
│ - Collect all type definitions                    │
│ - Check for duplicates                            │
│                                                    │
│ inference.rs:                                     │
│ - Lower expressions with type hints               │
│ - Annotate AST with partial type info             │
└───────────────────────────────────────────────────┘
    ↓
HIR (High-Level IR) with Type Annotations
    ↓
┌───────────────────────────────────────────────────┐
│ Type Checking Phase                               │
│                                                    │
│ checker_infer.rs:                                 │
│ - Infer types for all expressions                 │
│ - Generate constraints                            │
│                                                    │
│ checker_unify.rs:                                 │
│ - Solve constraints via unification               │
│ - Build substitution map                          │
│                                                    │
│ checker_check.rs:                                 │
│ - Validate final types                            │
│ - Check trait bounds                              │
│ - Verify exhaustiveness                           │
│                                                    │
│ Advanced Checkers (optional):                     │
│ - effects.rs: Track async/sync                    │
│ - dispatch_checker.rs: Validate dyn traits        │
│ - macro_checker.rs: Check macro expansions        │
└───────────────────────────────────────────────────┘
    ↓
Fully Typed HIR
    ↓
Monomorphization (generic specialization)
    ↓
Specialized HIR
    ↓
Codegen
```

**Key Properties:**
- **Multi-pass:** Separate registration, inference, validation
- **Incremental:** Can type-check incrementally
- **Comprehensive:** Checks all constructs
- **Integrated:** Part of full compilation pipeline

### Simple Type Unification Flow

```
Two Types (t1, t2)
    ↓
┌───────────────────────────────────────────────────┐
│ TypeUnifier.unify(t1, t2)                         │
│                                                    │
│ 1. Resolve both types                             │
│    - Follow substitution chains                   │
│                                                    │
│ 2. Check if equal                                 │
│    - Early return if same                         │
│                                                    │
│ 3. Match on type pair                             │
│    - Var-Var: link variables                      │
│    - Var-Concrete: occurs check + substitute      │
│    - Primitive-Primitive: check equality          │
│    - Function-Function: shallow check (buggy)     │
│    - Generic-Generic: shallow check (buggy)       │
│    - Else: fail                                   │
│                                                    │
│ 4. Return bool                                    │
│    - true: success                                │
│    - false: failure                               │
└───────────────────────────────────────────────────┘
    ↓
bool (success/failure)
```

**Key Properties:**
- **Single-pass:** One unification attempt
- **Standalone:** Not integrated with anything
- **Limited:** Only unifies explicit types
- **No inference:** Can't infer from expressions

---

## Extensibility Analysis

### Rust Extensibility

**Adding a New Type:**
```rust
// 1. Add to Type enum
pub enum Type {
    // ... existing variants
    NewType { field: String },
}

// 2. Handle in unification
impl TypeChecker {
    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), TypeError> {
        match (&t1, &t2) {
            // ... existing cases
            (Type::NewType { field: f1 }, Type::NewType { field: f2 }) if f1 == f2 => Ok(()),
            // ...
        }
    }
}

// 3. Handle in substitution
impl Type {
    pub fn apply_subst(&self, subst: &HashMap<usize, Type>) -> Type {
        match self {
            // ... existing cases
            Type::NewType { field } => Type::NewType { field: field.clone() },
            // ...
        }
    }
}

// 4. Add tests
#[test]
fn unify_new_type() { ... }
```

**Affected Files:** 3-4 files, ~50 lines total

### Simple Extensibility

**Adding a New Type:**
```simple
// 1. Add to Type enum
enum Type:
    # ... existing variants
    NewType(field: str)

// 2. Handle in unification
impl TypeUnifier:
    me unify(t1: Type, t2: Type) -> bool:
        match (resolved_t1, resolved_t2):
            # ... existing cases
            (Type.NewType(f1), Type.NewType(f2)) ->
                f1 == f2

// 3. Handle in to_string
impl Type:
    fn to_string() -> str:
        match self:
            # ... existing cases
            Type.NewType(field) -> "NewType({field})"

// 4. Add tests
check_test("NewType unifies", unifier.unify(NewType("x"), NewType("x")))
```

**Affected Files:** 1 file, ~10 lines total

**Comparison:**
- Simple is **easier to extend** (fewer files, less code)
- Rust is **more maintainable** (better separation, explicit contracts)

---

## Maintainability Comparison

| Aspect | Rust | Simple | Winner |
|--------|------|--------|--------|
| **Code Organization** | 15+ modules | 1 file | Rust (for large codebase) |
| **Separation of Concerns** | Excellent | Poor | Rust |
| **Testability** | Excellent | Basic | Rust |
| **Documentation** | Extensive | Minimal | Rust |
| **Ease of Extension** | Moderate | Easy | Simple (for small changes) |
| **Bug Localization** | Easy (modular) | Hard (monolithic) | Rust |
| **Onboarding** | Harder (many files) | Easier (1 file) | Simple |

**Verdict:** Rust wins for production, Simple wins for learning

---

## Conclusion

**Architecture Verdict:** Rust is **professionally architected**, Simple is **educational prototype**

**Key Findings:**
1. **Scale:** Rust 15+ modules (3,558 lines), Simple 1 module (309 lines) - 12x difference
2. **Integration:** Rust fully integrated into compiler pipeline, Simple standalone
3. **Extensibility:** Rust uses design patterns, Simple is basic class
4. **Maintainability:** Rust highly modular, Simple monolithic

**Recommendations:**
- **For Production:** Use Rust architecture (proven, maintainable, extensible)
- **For Teaching:** Use Simple architecture (easy to understand, single file)
- **For Self-Hosting:** Adopt Rust's modular approach, not Simple's monolith

---

**Documents:**
- **This Document:** `doc/analysis/type_inference_architecture.md`
- Error Reporting: `doc/analysis/type_inference_error_reporting.md`
- Test Coverage: `doc/analysis/type_inference_test_coverage.md`
- Performance: `doc/analysis/type_inference_performance.md`
- Feature Parity: `doc/analysis/type_inference_feature_parity.md`

**Status:** Phase 7 Complete ✅
**Next:** Phase 8 - Migration Roadmap (Final Phase)
