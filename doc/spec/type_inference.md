# Type Inference Specification

**Feature ID:** #13
**Status:** Partial Implementation (Hindley-Milner scaffold working)
**Difficulty:** 4
**Last Updated:** 2026-01-05

## Overview

Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring explicit type annotations in most cases.

## Goals

1. **Local Type Inference**: Infer types for let-bindings and function parameters
2. **Unification**: Determine type compatibility and solve type equations
3. **Polymorphism**: Support let-polymorphism for generic functions (planned)
4. **Pattern Matching**: Infer types from pattern destructuring
5. **Effect Tracking**: Track async/sync effects for concurrent code

## Type System

### Base Types

| Type | Description | Example |
|------|-------------|---------|
| `Int` | 64-bit signed integer | `42`, `-10` |
| `Float` | 64-bit floating point | `3.14`, `-0.5` |
| `Bool` | Boolean value | `true`, `false` |
| `Str` | String type | `"hello"`, `'raw'` |
| `Nil` | Null/none value | `nil` |

### Composite Types

| Type | Syntax | Description |
|------|--------|-------------|
| **Array** | `Array[T]` | Homogeneous collection: `[1, 2, 3]` |
| **Tuple** | `(T1, T2, ...)` | Heterogeneous product: `(1, "hi", true)` |
| **Dict** | `{K: V}` | Key-value mapping: `{"a": 1, "b": 2}` |
| **Function** | `(T1, T2) -> R` | Function type: `fn add(a, b) -> i64` |
| **Optional** | `T?` | Nullable value: `let x: i64? = nil` |
| **Union** | `T1 \| T2` | Sum type: `Int \| Str` |

### Advanced Types

| Type | Description |
|------|-------------|
| **Named** | Struct, class, or enum name: `Point`, `Color` |
| **Generic** | Parameterized type: `Box[T]`, `Result[T, E]` |
| **TypeParam** | Type parameter placeholder: `T`, `U` |
| **Borrow** | Immutable reference: `&T` |
| **BorrowMut** | Mutable reference: `&mut T` |
| **Simd** | SIMD vector: `vec[4, f32]` |
| **DynTrait** | Trait object: `dyn Show` |

## Inference Rules

### Literals

```simple
# Integer literals
let x = 42           # x: Int

# Float literals
let y = 3.14         # y: Float

# String literals
let s = "hello"      # s: Str

# Boolean literals
let b = true         # b: Bool

# Nil literal
let n = nil          # n: Nil
```

### Binary Operators

**Arithmetic Operators** (`+`, `-`, `*`, `/`, `%`, `**`, `//`, `@`):
- Both operands must have the same numeric type
- Result has the same type as operands

```simple
let a = 1 + 2        # a: Int (Int + Int -> Int)
let b = 3.0 * 1.5    # b: Float (Float * Float -> Float)
```

**Comparison Operators** (`==`, `!=`, `<`, `<=`, `>`, `>=`):
- Operands must have the same comparable type
- Result is always `Bool`

```simple
let cmp = 1 < 2      # cmp: Bool
```

**Logical Operators** (`and`, `or`):
- Both operands must be `Bool`
- Result is `Bool`

```simple
let logic = true and false  # logic: Bool
```

**Bitwise Operators** (`&`, `|`, `^`, `<<`, `>>`):
- Both operands must be `Int`
- Result is `Int`

```simple
let bits = 5 << 2    # bits: Int
```

### Unary Operators

| Operator | Type Constraint | Result Type |
|----------|-----------------|-------------|
| `-` | Operand: numeric | Same as operand |
| `not` | Operand: `Bool` | `Bool` |
| `~` | Operand: `Int` | `Int` |
| `&` | Any type `T` | `&T` (borrow) |
| `&mut` | Any type `T` | `&mut T` (mutable borrow) |
| `*` | `&T` or `&mut T` | `T` (deref) |

### Collections

**Arrays:**
```simple
let arr = [1, 2, 3]           # arr: Array[Int]
let empty: Array[Int] = []    # Explicit type for empty array
let nested = [[1, 2], [3, 4]] # nested: Array[Array[Int]]
```

**Tuples:**
```simple
let t = (1, "hi", true)       # t: (Int, Str, Bool)
let first = t[0]              # first: Int
```

**Dictionaries:**
```simple
let dict = {"a": 1, "b": 2}   # dict: {Str: Int}
let val = dict["a"]           # val: Int
```

### Functions

**Function Definition:**
```simple
# Inferred parameter and return types
fn add(a, b):
    return a + b              # Infers: (Int, Int) -> Int

# Explicit types
fn greet(name: str) -> str:
    return "Hello, " + name
```

**Function Calls:**
```simple
let result = add(1, 2)        # result: Int
```

**Higher-Order Functions:**
```simple
fn apply(f, x):
    return f(x)               # f: (T) -> R, x: T, return: R

fn inc(n):
    return n + 1              # inc: (Int) -> Int

let r = apply(inc, 5)         # r: Int
```

### Pattern Matching

**Match Expressions:**
```simple
enum Color:
    Red
    Green
    Blue(i64)

let c = Color::Blue(42)
match c:
    Color::Red =>
        0                     # Branch type: Int
    Color::Green =>
        1                     # Branch type: Int
    Color::Blue(val) =>
        val                   # Branch type: Int, val: Int
# Result type: Int (all branches unify)
```

**Destructuring:**
```simple
# Tuple pattern
let (x, y) = (1, 2)           # x: Int, y: Int

# Array pattern
let [a, b, c] = [1, 2, 3]     # a, b, c: Int

# Struct pattern
struct Point:
    x: i64
    y: i64

let Point { x, y } = Point { x: 1, y: 2 }  # x, y: i64
```

### Control Flow

**If Expressions:**
```simple
# Branches must unify to same type
let val = if x > 0:
    1                         # Branch 1: Int
else:
    2                         # Branch 2: Int
# Result: Int
```

**Loops:**
```simple
# While loop
let mut i = 0
while i < 10:
    i = i + 1

# For loop
for x in range(0, 10):        # x: Int (inferred from range)
    print(x)
```

## Type Unification

The type checker uses unification to determine type compatibility:

### Unification Rules

1. **Identical Types**: `T` unifies with `T`
2. **Type Variables**: `Var(n)` unifies with any type `T` (with occurs check)
3. **Arrays**: `Array[T1]` unifies with `Array[T2]` if `T1` unifies with `T2`
4. **Tuples**: `(T1, T2)` unifies with `(U1, U2)` if `T1 ~ U1` and `T2 ~ U2`
5. **Functions**: `(P1, P2) -> R1` unifies with `(Q1, Q2) -> R2` if all params and returns unify
6. **Generics**: `Generic[T, U]` unifies with `Generic[V, W]` if `T ~ V` and `U ~ W`

### Occurs Check

Prevents infinite types:
```simple
# This would fail: T = Array[T]
let x = [x]  # Error: occurs check failed
```

### Substitution

Type variables are resolved through substitution:
```simple
let arr = []           # arr: Array[?T]
arr[0] = 42            # Unify ?T with Int
# arr: Array[Int]
```

## Current Implementation Status

### ✅ Implemented

- [x] Basic type inference for literals
- [x] Binary and unary operator inference
- [x] Array, tuple, and dictionary inference
- [x] Function type inference
- [x] Pattern matching inference
- [x] Unification with occurs check
- [x] Substitution tracking
- [x] Effect inference (async/sync)
- [x] Struct/class/enum registration
- [x] Method calls and field access
- [x] Trait definitions and implementations
- [x] Macro type checking
- [x] Borrow and ownership types

### 🔄 Partially Implemented

- [ ] Type scheme generalization
- [ ] Type scheme instantiation
- [ ] Let-polymorphism
- [ ] Generic type instantiation
- [ ] Type parameter constraints

### 📋 Planned

- [ ] Better error messages with source spans
- [ ] Type annotations for better error reporting
- [ ] Integration with HIR for native codegen
- [ ] SIMD type inference
- [ ] GPU kernel type checking

## Formal Verification

### Lean 4 Model

The type inference system has a formally verified core in Lean 4 (see `verification/type_inference_compile/`):

```lean
-- Lean type inference function
def infer : Expr → Option Ty
  | litNat _ => some Ty.nat
  | litBool _ => some Ty.bool
  | add a b => do
      let Ty.nat ← infer a | none
      let Ty.nat ← infer b | none
      pure Ty.nat
  | ifElse c t e => do
      let Ty.bool ← infer c | none
      let τt ← infer t
      let τe ← infer e
      if τt = τe then pure τt else none
```

**Verified Properties:**
- **Determinism**: Inference returns at most one type
- **Soundness**: Inferred types are correct with respect to typing rules
- **Progress**: Well-typed expressions can be evaluated

### Rust Implementation Mapping

The Rust implementation (`src/type/src/lib.rs`) includes:
1. **Pure Inference**: `lean_infer()` matches Lean model exactly
2. **Full Inference**: `TypeChecker::infer_expr()` extends pure model
3. **Bridge**: `to_simple_expr()` converts AST to Lean model when possible

## Testing Strategy

### Test Coverage

**Unit Tests** (`src/type/tests/`):
- `inference.rs`: 76 tests covering core inference
- `async_default_integration.rs`: 9 tests for effect inference
- `advanced_inference.rs`: 43 tests for edge cases and Lean model

**Total**: 128 tests

### Test Categories

1. **Lean Model Tests**: Pure inference matching formal spec (15 tests)
2. **Basic Inference**: Literals, operators, collections (30 tests)
3. **Functions**: Definitions, calls, recursion, higher-order (15 tests)
4. **Patterns**: Destructuring, match expressions (10 tests)
5. **Control Flow**: If, while, for, loop (8 tests)
6. **Advanced Types**: Generics, traits, macros (15 tests)
7. **Error Cases**: Type mismatches, undefined variables (10 tests)
8. **Substitution**: Type variable resolution, occurs check (5 tests)
9. **Effects**: Async/sync inference, suspension operators (9 tests)
10. **Edge Cases**: Nested types, coercion, polymorphism (11 tests)

### Running Tests

```bash
# All type inference tests
cargo test -p simple-type

# Specific test file
cargo test -p simple-type --test inference
cargo test -p simple-type --test advanced_inference

# Specific test
cargo test -p simple-type infers_let_and_function_return
```

## Examples

### Example 1: Basic Inference

```simple
# All types inferred automatically
let numbers = [1, 2, 3, 4, 5]      # Array[Int]
let sum = 0                         # Int
for n in numbers:                   # n: Int
    sum = sum + n
# sum: Int
```

### Example 2: Higher-Order Functions

```simple
fn map(f, arr):
    let result = []
    for x in arr:
        result.append(f(x))
    return result

fn double(x):
    return x * 2

let nums = [1, 2, 3]               # Array[Int]
let doubled = map(double, nums)    # Array[Int]
```

### Example 3: Pattern Matching

```simple
enum Option[T]:
    Some(T)
    None

fn unwrap_or(opt, default):
    match opt:
        Option::Some(val) =>
            val                    # Type inferred from T
        Option::None =>
            default                # Must unify with T
# Return type: T
```

### Example 4: Effect Inference

```simple
# Async by default
fn fetch_data():
    let response = http.get("https://api.example.com")  # Async call
    return response.json()
# Inferred as async

# Explicit sync
sync fn compute():
    return 2 + 2
# Explicitly sync
```

## Error Messages

### Type Mismatch

```simple
let x = 1 + "hello"
# Error: Type mismatch
#   Expected: Int
#   Found: Str
```

### Undefined Variable

```simple
let result = unknown_var + 1
# Error: Undefined identifier: unknown_var
```

### Occurs Check

```simple
let x = [x]
# Error: Occurs check failed
#   Cannot unify Var(0) with Array[Var(0)]
#   This would create an infinite type
```

## Integration with Compiler Pipeline

```
Source Code
    ↓
  Lexer
    ↓
  Parser → AST
    ↓
Type Checker ← (Type Inference happens here)
    ↓
  HIR (Type-annotated IR)
    ↓
  MIR
    ↓
 Codegen
```

The type checker runs after parsing and before lowering to HIR. It validates that all expressions are well-typed and annotates the AST with type information for later compilation stages.

## References

- **Design**: `doc/design/type_inference.md`
- **Status**: `doc/status/type_inference.md`
- **Implementation**: `src/type/src/lib.rs`
- **Tests**: `src/type/tests/`
- **Formal Verification**: `verification/type_inference_compile/`
- **Lean 4 Model**: `verification/type_inference_compile/src/TypeInferenceCompile.lean`

## Future Enhancements

1. **Polymorphic Type Inference**: Full let-polymorphism with generalization
2. **Type Classes**: Advanced trait constraints
3. **Dependent Types**: For array bounds and invariants
4. **Linear Types**: For resource management
5. **Effect System**: Extended effect tracking beyond async/sync
6. **Refinement Types**: For contracts and predicates
7. **Gradual Typing**: Mix of static and dynamic typing
