# Safe Unwrap Operators Specification

**Feature ID:** #OPERATORS-SAFE-UNWRAP | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/safe_unwrap_operators_spec.spl`_

---

## Syntax

```simple
opt unwrap or: default_value              # Use default if None
opt unwrap else: \: lazy_default_expr     # Lazy evaluation of default
result unwrap or_return: default_on_err   # Early return with default
```

## Key Behaviors

- `unwrap or:` evaluates the default value immediately (eager)
- `unwrap else:` takes a closure for lazy evaluation (only called if needed)
- `unwrap or_return:` returns from the function with a default value on error
- Works with both Option<T> and Result<T, E> types
- Provides inline alternatives to verbose pattern matching
- Type-safe: never causes runtime panics

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 23 |

## Test Structure

### Safe Unwrap Operators

#### unwrap or: with eager evaluation

- ✅ returns value when Option is Some
- ✅ returns default when Option is None
- ✅ works with Result Ok
- ✅ returns default for Result Err
- ✅ evaluates default expression
- ✅ handles complex default expressions
- ✅ works with string defaults
- ✅ preserves value type through unwrap
#### unwrap else: with lazy evaluation

- ✅ returns value when Option is Some without calling closure
- ✅ calls closure only when Option is None
- ✅ works with Result Ok without evaluating closure
- ✅ evaluates closure for Result Err
- ✅ closure can perform side effects
- ✅ lazy evaluation skips expensive computation when value exists
#### unwrap or_return: with early return

- ✅ returns value when present
- ✅ returns default when None
- ✅ works with Result
- ✅ returns default for Result Err
#### chaining and composition

- ✅ can chain multiple unwrap operations
- ✅ works in nested expressions
#### type safety

- ✅ preserves Option type semantics
- ✅ handles nested Option types
- ✅ preserves Result error information

