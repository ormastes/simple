# Feature: Type Inference (Feature #13)

**Status**: Complete (Basic HM-style)
**Difficulty**: 4 (was 5)
**Importance**: 4

## Summary

Hindley-Milner-style local inference for lets/functions with unification.

## Implementation

The `simple-type` crate provides:
- [x] Type enum (Int, Bool, Str, Float, Nil, Var, Function, Array, Union, Generic, etc.)
- [x] TypeChecker with environment
- [x] Fresh type variable generation
- [x] **Unification algorithm** with occurs check
- [x] **Substitution** data structure for tracking solved type variables
- [x] Expression type inference for literals, identifiers
- [x] **Binary operator inference** with proper type rules:
  - Arithmetic: both operands unify, result is operand type
  - Comparison: operands unify, result is Bool
  - Logical: operands unify with Bool, result is Bool
  - Bitwise: operands unify with Int, result is Int
- [x] Array inference with element unification
- [x] **If expression** inference with branch unification
- [x] **Index expression** inference (array → element type)
- [x] **Function call** inference with param/arg unification
- [x] Pattern matching with guards
- [x] Function/struct/class/enum registration in environment

## Key Components

### Substitution
Tracks type variable assignments:
```rust
pub struct Substitution {
    map: HashMap<usize, Type>,
}
```

### Unification
Unifies two types, updating the substitution:
```rust
pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), TypeError>
```

### Type Application
Applies substitution to resolve type variables:
```rust
pub fn apply_subst(&self, subst: &Substitution) -> Type
```

### Occurs Check
Prevents infinite types like `T = Array<T>`:
```rust
pub fn contains_var(&self, var_id: usize) -> bool
```

## Example Inference

```simple
# Integer literals → Int
let x = 42

# Binary ops unify operands
let y = x + 10  # x: Int, 10: Int → y: Int

# Array elements unify
let arr = [1, 2, 3]  # arr: Array<Int>

# Function calls propagate types
fn double(n: i64) -> i64:
    return n * 2
let z = double(x)  # z: i64
```

## Tests

- `infers_let_and_function_return` - Basic let and function inference
- `catches_undefined_variable` - Error on undefined variables

## Files

- `src/type/src/lib.rs` - Main type checker implementation (~750 lines)

## Future Work

- [ ] Generalization at let-binding (polymorphic lets)
- [ ] Instantiation at use sites (fresh copies of polymorphic types)
- [ ] Better error reporting with span information
- [ ] Integration with interpreter for runtime type checks

## Why Difficulty Reduced (5→4)

- TypeChecker crate already had basic infrastructure
- Unification and type variable infrastructure was partially in place
- Core HM algorithm is well-understood
- Remaining work was incremental, not from scratch
