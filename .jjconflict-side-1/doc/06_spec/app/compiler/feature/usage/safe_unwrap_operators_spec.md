# Safe Unwrap Operators Specification

Safe unwrap operators provide ergonomic ways to extract values from Option<T>

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OPERATORS-SAFE-UNWRAP |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/safe_unwrap_operators_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Safe unwrap operators provide ergonomic ways to extract values from Option<T>
and Result<T, E> types with default fallbacks or error handling. They eliminate
the need for manual pattern matching in common cases while remaining type-safe.

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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/safe_unwrap_operators/result.json` |

## Scenarios

- returns value when Option is Some
- returns default when Option is None
- works with Result Ok
- returns default for Result Err
- evaluates default expression
- handles complex default expressions
- works with string defaults
- preserves value type through unwrap
- returns value when Option is Some without calling closure
- calls closure only when Option is None
- works with Result Ok without evaluating closure
- evaluates closure for Result Err
- closure can perform side effects
- lazy evaluation skips expensive computation when value exists
- returns value when present
- returns default when None
- works with Result
- returns default for Result Err
- can chain multiple unwrap operations
- works in nested expressions
- preserves Option type semantics
- handles nested Option types
- preserves Result error information
