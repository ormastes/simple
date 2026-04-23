# Optional Chaining Specification

Optional chaining (`?.`) provides safe navigation through potentially-nil

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OPERATORS-OPTIONAL-CHAIN |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/optional_chaining_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Optional chaining (`?.`) provides safe navigation through potentially-nil
values in object graphs and method call chains. It automatically propagates
None values through the chain without requiring manual null checks at each step.

## Syntax

```simple
obj?.field               # Safe field access - returns Option
obj?.method()            # Safe method call - returns Option
obj?.field?.nested?.deep # Safe chaining - short-circuits on None
```

## Key Behaviors

- Optional chaining returns Option<T> for chained operations
- Returns None immediately if any intermediate value is None
- Prevents null pointer exceptions and NullPointerException-style errors
- Works with both field access and method calls
- Can be chained multiple times
- Integrates with null coalescing (`??`) for fallback values

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/optional_chaining/result.json` |

## Scenarios

- returns Some when value is present
- returns None when intermediate value is None
- works with deeply nested structures
- short-circuits on first None in chain
- calls method when value is Some
- returns None when Option is None
- works with chained method calls
- handles methods with parameters
- combines field and method access
- chains field access followed by field access
- provides fallback when chaining returns None
- uses actual value when chaining succeeds
- chains multiple fallbacks
- wraps return value in Option
- preserves complex types through chaining
- works with collection methods
- handles None in collection operations
- simplifies conditional access patterns
- provides defensive programming in data processing
- enables safe navigation in unknown data structures
