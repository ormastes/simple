# Existence Check Operator (.?) Specification

**Feature ID:** #2100 | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/exists_check_spec.spl`_

---

The `.?` operator checks if a value is "present" (non-nil AND non-empty).

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 17 |

## Test Structure

### Existence Check Operator .?

#### Option type

- ✅ returns true for Some
- ✅ returns true for Some(0)
- ✅ returns false for None
#### List type

- ✅ returns false for empty list
- ✅ returns true for non-empty list
#### Dict type

- ✅ returns false for empty dict
- ✅ returns true for non-empty dict
#### String type

- ✅ returns false for empty string
- ✅ returns true for non-empty string
#### Primitive types

- ✅ returns true for positive number
- ✅ returns true for zero
- ✅ returns true for false
#### with no-paren method calls

- ✅ works with list.first.?
- ✅ returns false for empty list.first.?
- ✅ works with string.trim.?
- ✅ works with chained no-paren methods
- ✅ returns false for empty result

