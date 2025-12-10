# Feature #13: Type Inference

**Status**: Interpreter: Working | Type Checker: Partial HM scaffold
**Difficulty**: 4 (was 5)
**Importance**: 4

## Summary

Hindley-Milner-style local inference for lets/functions with unification. The type checker validates code before interpretation.

## Implementation

The `simple-type` crate provides:
- [x] Type enum (Int, Bool, Str, Float, Nil, Var, Function, Array, Union, Generic, etc.)
- [x] TypeChecker with environment
- [x] Fresh type variable generation
- [x] **Unification algorithm** with occurs check
- [x] **Substitution** data structure for tracking solved type variables
- [x] Expression type inference for literals, identifiers
- [x] **Binary operator inference** with proper type rules
- [x] Array inference with element unification
- [x] **If expression** inference with branch unification
- [x] **Index expression** inference (array → element type)
- [x] **Function call** inference with param/arg unification
- [x] Pattern matching with guards
- [x] Function/struct/class/enum registration in environment

## Architecture

```
Source → Parser → AST → Type Checker → Interpreter
                              ↓
                   Validates types before execution
```

The type checker runs before the interpreter but doesn't yet feed types to a native codegen pipeline.

## Key Components

### Substitution
```rust
pub struct Substitution {
    map: HashMap<usize, Type>,
}
```

### Unification
```rust
pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), TypeError>
```

### Occurs Check
Prevents infinite types like `T = Array<T>`.

## Example

```simple
let x = 42           # x: Int (inferred)
let y = x + 10       # y: Int (unification)
let arr = [1, 2, 3]  # arr: Array<Int>
```

## Tests

```bash
cargo test -p simple-type
```

- `infers_let_and_function_return`
- `catches_undefined_variable`

## Files

- `src/type/src/lib.rs` - Type checker (~750 lines)
- `src/compiler/src/pipeline.rs` - Calls type_check before interpreter

## Future Work

- [ ] Generalization at let-binding (polymorphic lets)
- [ ] Instantiation at use sites
- [ ] Integration with HIR for native codegen
- [ ] Better error messages with source spans

## Why Difficulty Reduced (5→4)

- Core HM infrastructure exists
- Unification and substitution working
- Remaining work is polish, not foundational
