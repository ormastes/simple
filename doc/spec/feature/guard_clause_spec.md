# Guard Clause Specification

**Feature ID:** #GUARD-CLAUSE | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/guard_clause_spec.spl`_

---

## Syntax

```simple
match value:
    case pattern if condition:
        body
```

## Key Behaviors

- Guard conditions are evaluated after pattern matching succeeds
- Variables bound in the pattern are available in the guard condition
- If the guard evaluates to false, matching continues to the next arm
- Guards can reference external variables from the enclosing scope

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 10 |

## Test Structure

### Guard Clauses

#### basic integer guards

- ✅ matches when guard is true
- ✅ falls through when guard is false
- ✅ reaches default case when all guards fail
#### guards with equality checks

- ✅ matches exact value via guard
#### guards with tuple patterns

- ✅ uses bound variables in guard
- ✅ guards with multiple comparisons
#### guards with enum patterns

- ✅ filters enum payload with guard
#### guards with external variables

- ✅ references variables from outer scope
#### guards with complex expressions

- ✅ uses modulo in guard
- ✅ uses logical or in guard

