# Optional Chaining Specification

**Feature ID:** #OPERATORS-OPTIONAL-CHAIN | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/optional_chaining_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 20 |

## Test Structure

### Optional Chaining

#### optional field access

- ✅ returns Some when value is present
- ✅ returns None when intermediate value is None
- ✅ works with deeply nested structures
- ✅ short-circuits on first None in chain
#### optional method calls

- ✅ calls method when value is Some
- ✅ returns None when Option is None
- ✅ works with chained method calls
- ✅ handles methods with parameters
#### chaining field and method access

- ✅ combines field and method access
- ✅ chains field access followed by field access
#### with null coalescing operator

- ✅ provides fallback when chaining returns None
- ✅ uses actual value when chaining succeeds
- ✅ chains multiple fallbacks
#### type preservation

- ✅ wraps return value in Option
- ✅ preserves complex types through chaining
#### integration with other features

- ✅ works with collection methods
- ✅ handles None in collection operations
#### practical usage patterns

- ✅ simplifies conditional access patterns
- ✅ provides defensive programming in data processing
- ✅ enables safe navigation in unknown data structures

