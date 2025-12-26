# Feature #34: Macros

**Status**: Implemented
**Difficulty**: 4 (was 5)
**Importance**: 3

## Summary

Compile-time macros for code generation and metaprogramming. Both built-in macros and user-defined macros are working.

## Planned Syntax

```simple
# Definition
macro debug!(expr):
    print(f"DEBUG: {stringify!(expr)} = {expr}")

# Usage
debug!(some_value)
# Expands to: print(f"DEBUG: some_value = {some_value}")

# Pattern matching macros
macro vec![...items]:
    Array.from([...items])
```

## Features Implemented

- [x] Macro definition syntax (`macro name!($params):`)
- [x] Pattern-based expansion with `$param` substitution
- [x] Built-in macros: `println!`, `print!`, `vec!`, `assert!`, `assert_eq!`, `format!`, `dbg!`, `panic!`
- [x] User-defined macros with block bodies
- [x] Macro parameter substitution in expressions and statements
- [x] Parser-friendly surface: macro defs and invocations are explicit AST nodes; macro names are tracked for dependency analysis
- [ ] Hygiene (avoid name collisions) - future enhancement
- [ ] `stringify!` for expression text - future enhancement
- [ ] Variadic patterns (`...`) - partially supported
- [ ] Recursive macros - not tested

## Why Difficulty Reduced (5→4)

- Macro expansion is additive (doesn't affect existing code)
- Can start with simple textual macros
- Parser already handles complex syntax
- Well-documented pattern from Rust/Lisp
- Can defer hygiene to later iteration

## Dependencies

- Requires macro expansion pass before parsing/type checking
- AST manipulation infrastructure
- Scope hygiene tracking (can defer)

## Implementation Approach

1. Add macro definition syntax to parser
2. Implement simple pattern matching
3. Add expansion pass before main parsing
4. Start with non-hygienic macros (simpler)
5. Add hygiene in later iteration

## Complexity

Requires:
- Macro parser (different from main parser)
- AST splicing
- Hygiene algorithm (can defer)
- Error reporting through macro expansion

## Simplification Option

Start with simple substitution macros:
```simple
macro PI = 3.14159
macro MAX(a, b) = if a > b: a else: b
```

## Related

- May interact with all language features
