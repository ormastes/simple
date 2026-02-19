# Multiple Assignment (Destructuring) Specification

**Feature ID:** #MULTIPLE-ASSIGNMENT | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/multiple_assignment_spec.spl`_

---

## Syntax

```simple
# Tuple destructuring
val (x, y) = get_point()
val (first, second, ...rest) = items

# Array destructuring
val [a, b, c] = triple

# Struct destructuring
val {name, age} = person
```

## Key Behaviors

- Pattern must match the structure of the value
- Variables are bound in the order they appear
- Wildcards `_` can ignore unwanted values
- Rest patterns `...rest` capture remaining elements

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 18 |

## Test Structure

### Multiple Assignment (Destructuring)

#### tuple destructuring

- ✅ destructures a pair
- ✅ destructures a triple
- ✅ uses destructured values in expressions
- ✅ destructures function return value
#### tuple destructuring with wildcards

- ✅ ignores first element with wildcard
- ✅ ignores middle element with wildcard
- ✅ ignores last element with wildcard
- ✅ ignores multiple elements
#### nested tuple destructuring

- ✅ destructures nested tuples
- ✅ destructures deeply nested tuples
#### array destructuring

- ✅ destructures fixed-size array
- ✅ destructures with wildcard
#### mutable destructuring

- ✅ creates mutable bindings
- ✅ allows partial mutation
#### mixed type destructuring

- ✅ destructures tuples with different types
- ✅ destructures nested mixed types
#### destructuring in loops

- ✅ destructures in for loop
- ✅ uses destructured values for computation

