# Struct Field Shorthand Specification

**Feature ID:** #STRUCT-SHORTHAND | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/struct_shorthand_spec.spl`_

---

## Syntax

```simple
# Without shorthand (verbose)
val point = Point(x: x, y: y)

# With shorthand (when variable names match field names)
val point = Point(x, y)

# Mixed shorthand and explicit
val point = Point(x, y: computed_y)
```

## Key Behaviors

- Variable name must exactly match the field name
- Order must match the struct definition
- Can mix shorthand and explicit field names
- Works with any struct type

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### Struct Field Shorthand

#### basic struct shorthand

- ✅ uses shorthand for matching variable names
- ✅ constructs struct with all shorthand fields
#### mixed shorthand and explicit

- ✅ mixes shorthand with explicit named argument
- ✅ uses explicit then shorthand
- ✅ mixes in complex struct
#### shorthand with computed values

- ✅ uses shorthand after computation
- ✅ uses shorthand from function return
#### shorthand with different types

- ✅ handles text fields
- ✅ handles boolean fields
- ✅ handles mixed types
#### shorthand in nested structs

- ✅ uses shorthand when nesting
#### explicit syntax still works

- ✅ allows fully explicit construction
- ✅ allows equals syntax explicitly
#### shorthand in collections

- ✅ uses shorthand in list of structs
- ✅ uses shorthand with map

