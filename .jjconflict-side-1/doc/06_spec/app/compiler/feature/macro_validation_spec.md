# Macro Validation Specification

**Feature ID:** #MACRO-VAL-001 to #MACRO-VAL-014 | **Category:** Infrastructure | Macros | **Status:** Implemented

_Source: `test/feature/usage/macro_validation_spec.spl`_

---

## Error Codes

- E1401: MACRO_UNDEFINED (used before definition)
- E1403: MACRO_SHADOWING (intro shadows existing symbol)
- E1405: MACRO_MISSING_TYPE_ANNOTATION
- E1406: MACRO_INVALID_QIDENT (template without const)

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 14 |

## Test Structure

### Macro Definition Order

- ✅ succeeds when macro is defined before use
- ✅ fails when macro is used before definition
### Intro Shadowing Detection

- ✅ fails when intro shadows existing variable
- ✅ fails when intro shadows existing function
- ✅ succeeds when intro introduces different symbol
### QIDENT Template Validation

- ✅ succeeds with const parameter in template
- ✅ fails when template variable is not const
### Type Annotation Requirements

- ✅ fails when intro let lacks type annotation
- ✅ succeeds when intro let has type annotation
### Multiple Macros Ordering

- ✅ allows using macros in any order after definition
### Multiple Intro Symbols

- ✅ allows single intro symbol
- ✅ fails when macro introduces duplicate symbols
### Intro For Loop

- ✅ generates symbols from const for loop
### Intro Conditional

- ✅ selects symbols based on const condition

