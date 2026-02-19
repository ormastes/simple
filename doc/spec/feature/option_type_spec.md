# Option Type Specification

**Feature ID:** #OPT-001 | **Category:** Language | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/option_type_spec.spl`_

---

## Overview

Tests for the Option type representing values that may or may not be present,
including constructors, pattern matching, and safe unwrapping mechanisms.

## Syntax

```simple
val maybe_value: Option<i32> = Some(42)
val no_value: Option<text> = nil

match maybe_value:
    Some(x) => print "Value is {x}"
    None => print "No value"

val unwrapped = maybe_value.unwrap()           # Raises if None
val safe = maybe_value.unwrap_or(0)            # Default if None
val mapped = maybe_value.map(\x: x * 2)        # Transform if Some
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Some | Option containing a value |
| None | Option representing absence of value |
| Unwrapping | Extracting value from Option |
| Safe Unwrap | Get value or default/error handling |
| Composition | Chaining operations on Options |

## Behavior

- Option<T> is generic over type T
- Some(value) contains a value of type T
- None represents absence (no value)
- Pattern matching provides exhaustive case handling
- map/filter/flat_map for functional composition
- unwrap() raises error, unwrap_or() provides default value
- Existence check with .? operator

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### Option Type Basic Usage

#### Some values

- ✅ creates Some with value
- ✅ checks Some is some
#### None values

- ✅ creates None
- ✅ uses unwrap_or for None
### Option Type Transformations

- ✅ maps Some value
- ✅ maps None returns None
### Existence Check Operator

- ✅ returns true for Some
- ✅ returns false for None

