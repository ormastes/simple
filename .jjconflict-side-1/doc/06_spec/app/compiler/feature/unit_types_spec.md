# Unit Types Specification

**Feature ID:** #UNIT-001 | **Category:** Language | Types | **Status:** Implemented

_Source: `test/feature/usage/unit_types_spec.spl`_

---

## Overview

Tests for semantic unit types that add compile-time dimensional safety
to numeric values.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 19 |

## Test Structure

### Standalone Units

- ✅ defines standalone unit type
- ✅ performs arithmetic with units
- ✅ gets value from unit
- ✅ gets suffix from unit
- ✅ converts unit to string
### Unit Families

- ✅ defines unit family
### Unit Arithmetic

- ✅ allows same-family addition
- ✅ allows same-family subtraction
- ✅ allows scaling by scalar
- ✅ allows comparison always
### Compound Units

- ✅ defines compound unit
- ✅ computes velocity from division
- ✅ cancels same units in division
- ✅ defines area from multiplication
### SI Prefixes

- ✅ uses kilo prefix
- ✅ uses mega prefix
- ✅ uses milli prefix
### Unit Type Inference

- ✅ accepts correct unit parameter
- ✅ returns correct unit type

