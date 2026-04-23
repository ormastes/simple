# Multiple Assignment (Destructuring) Specification

Multiple assignment (destructuring) allows binding multiple variables from

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MULTIPLE-ASSIGNMENT |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/multiple_assignment_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Multiple assignment (destructuring) allows binding multiple variables from
compound values like tuples, arrays, and structs in a single statement.
This provides concise syntax for unpacking data structures.

## Syntax

```simple
val (x, y) = get_point()
val (first, second, ...rest) = items

val [a, b, c] = triple

val {name, age} = person
```

## Key Behaviors

- Pattern must match the structure of the value
- Variables are bound in the order they appear
- Wildcards `_` can ignore unwanted values
- Rest patterns `...rest` capture remaining elements

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/multiple_assignment/result.json` |

## Scenarios

- destructures a pair
- destructures a triple
- uses destructured values in expressions
- destructures function return value
- ignores first element with wildcard
- ignores middle element with wildcard
- ignores last element with wildcard
- ignores multiple elements
- destructures nested tuples
- destructures deeply nested tuples
- destructures fixed-size array
- destructures with wildcard
- creates mutable bindings
- allows partial mutation
- destructures tuples with different types
- destructures nested mixed types
- destructures in for loop
- uses destructured values for computation
