# Feature: Generics (Feature #14)

**Status**: Complete (Basic)
**Difficulty**: 4 (was 5)
**Importance**: 4

## Summary

Generic type parameters on functions and types with monomorphization.

## Implementation

- [x] Parser accepts generic type forms `Type<A, B>`
- [x] AST: `Type::Generic { name, args }`
- [x] Type variables in type checker (`Type::Var(usize)`)
- [x] Fresh variable generation for instantiation
- [x] Generic parameter parsing on function definitions: `fn foo<T>(...)`
- [x] Generic parameter parsing on struct definitions: `struct Box<T>:`
- [x] Generic parameter parsing on enum definitions: `enum Maybe<T>:`
- [x] Generic parameter parsing on class definitions: `class Container<T>:`
- [x] Generic parameter parsing on trait definitions: `trait Functor<F>:`
- [x] Runtime works via dynamic typing (no monomorphization needed for interpreter)

## Working Syntax

```simple
# Generic function
fn identity<T>(x: T) -> T:
    return x

let n = identity(42)  # Returns 42

# Multiple type parameters
fn first<A, B>(a: A, b: B) -> A:
    return a

# Generic struct
struct Box<T>:
    value: T

let b = Box { value: 42 }
print(b.value)  # 42

# Generic enum
enum Maybe<T>:
    Just(T)
    Nothing

# Note: Generic type arguments in type positions use [] not <>
fn get_or_default(m: Maybe[i64], default: i64) -> i64:
    match m:
        Maybe::Just(v) =>
            return v
        Maybe::Nothing =>
            return default
    return default

let x = Maybe::Just(42)
get_or_default(x, 0)  # Returns 42
```

## Tests

- `interpreter_generic_function_identity` - Basic generic function
- `interpreter_generic_function_pair` - Multiple type parameters
- `interpreter_generic_struct` - Generic struct definition
- `interpreter_generic_enum` - Generic enum with pattern matching

## Files

- `src/parser/src/ast.rs` - `FunctionDef.generic_params`, `StructDef.generic_params`, etc.
- `src/parser/src/parser.rs` - `parse_generic_params()`, updated all definition parsers
- `src/type/src/lib.rs` - `Type::Generic`, `Type::TypeParam`

## Future Work

- [ ] Monomorphization pass for codegen optimization
- [ ] Instantiation cache to avoid duplicate code
- [ ] Symbol name mangling for monomorphized instances
- [ ] Trait bounds on generics: `fn max<T: Ord>(a: T, b: T) -> T`

## Why Difficulty Reduced (5→4)

- Parser already handles `Type::Generic`
- Type variable infrastructure exists in simple-type
- Monomorphization is a straightforward transformation
- No need to implement full parametric polymorphism (can monomorphize)
