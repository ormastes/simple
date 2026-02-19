# Single-Line Function Definitions Specification

**Feature ID:** #SYNTAX-INLINE | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/single_line_functions_spec.spl`_

---

## Syntax

```simple
fn name(): implicit_return_expr
fn name(param: Type) -> ReturnType: expr
```

## Key Behaviors

- Single-line functions have an implicit return expression (no explicit `return` needed)
- The expression is evaluated and returned automatically
- Explicit return types are optional but supported
- Works with zero, one, or multiple parameters
- Compatible with class methods and static functions
- Traditional block syntax is still supported and can be mixed in the same file

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 19 |

## Test Structure

### Single-Line Function Definitions

#### basic syntax

- ✅ parses inline expression body
- ✅ parses with multiple parameters
- ✅ parses with no parameters
- ✅ handles complex expressions
- ✅ returns immediately without explicit return
#### with explicit return types

- ✅ supports explicit return type annotation
- ✅ works with function parameter types
- ✅ infers return type from expression
#### with method definitions

- ✅ works with class methods
- ✅ works with mutable methods
- ✅ works with static functions
#### with collection operations

- ✅ works with lambda-like expressions
- ✅ handles filtering in single line
#### mixing with block syntax

- ✅ can coexist with traditional block functions
- ✅ block functions still work normally
- ✅ allows either style in same module
#### edge cases

- ✅ works with nested function calls
- ✅ handles string expressions
- ✅ works with conditional expressions

