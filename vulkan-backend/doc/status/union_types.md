# Feature #37: Union Types

**Status**: Complete
**Difficulty**: 2 (was 4)
**Importance**: 3

## Summary

Union types allow a value to be one of several types, using `A | B` syntax.

## Implementation

- [x] Union type syntax in annotations `A | B`
- [x] Parser support for union types
- [x] Multiple types in union `A | B | C`
- [x] AST: `Type::Union(Vec<Type>)`
- [x] Type checker: `Type::Union(Vec<Type>)` with compatibility checking
- [x] Runtime type checking via `Value::matches_type()`
- [x] Pattern matching on union types with `n: i64 =>` syntax
- [x] Typed patterns in pattern matching

## Working Syntax

```simple
# Union type annotation in function parameters
fn process(x: i64 | str) -> i64:
    return 42

# Function accepts either int or string
process(10)
process("hello")

# Pattern matching with type discrimination
fn classify(x: i64 | str | bool) -> i64:
    match x:
        n: i64 =>
            return 1
        s: str =>
            return 2
        b: bool =>
            return 3
    return 0

# Each branch matches the specific type
classify(42)      # returns 1
classify("test")  # returns 2
classify(true)    # returns 3
```

## Tests

- `interpreter_union_type_annotation` - Basic union type annotation
- `interpreter_union_type_pattern_match_int` - Match integer in union
- `interpreter_union_type_pattern_match_str` - Match string in union
- `interpreter_union_type_three_types` - Union with three types

## Files

- `src/parser/src/parser.rs` - `parse_type()` handles `|`, `parse_pattern()` handles typed patterns
- `src/parser/src/ast.rs` - `Type::Union(Vec<Type>)`, `Pattern::Typed`
- `src/type/src/lib.rs` - `Type::Union`, `types_compatible()`, `type_matches_union()`
- `src/compiler/src/lib.rs` - `Value::matches_type()`, `Pattern::Typed` handling

## Future Work

- Type narrowing in if/else branches (TypeScript-style)
- Exhaustiveness checking for union patterns
