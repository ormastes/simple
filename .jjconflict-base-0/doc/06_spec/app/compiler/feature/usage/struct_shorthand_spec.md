# Struct Field Shorthand Specification

Struct field shorthand allows omitting the field name when the variable name

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STRUCT-SHORTHAND |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/struct_shorthand_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Struct field shorthand allows omitting the field name when the variable name
matches. This reduces boilerplate when constructing structs from local variables.

## Syntax

```simple
val point = Point(x: x, y: y)

val point = Point(x, y)

val point = Point(x, y: computed_y)
```

## Key Behaviors

- Variable name must exactly match the field name
- Order must match the struct definition
- Can mix shorthand and explicit field names
- Works with any struct type

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/struct_shorthand/result.json` |

## Scenarios

- uses shorthand for matching variable names
- constructs struct with all shorthand fields
- mixes shorthand with explicit named argument
- uses explicit then shorthand
- mixes in complex struct
- uses shorthand after computation
- uses shorthand from function return
- handles text fields
- handles boolean fields
- handles mixed types
- uses shorthand when nesting
- allows fully explicit construction
- allows equals syntax explicitly
- uses shorthand in list of structs
- uses shorthand with map
