# Unnamed Duplicate Typed Arguments Warning Specification

**Feature ID:** #LINT-001 | **Category:** Lint | **Status:** Implemented

_Source: `test/feature/usage/unnamed_duplicate_typed_args_spec.spl`_

---

use std.text.{NL}

This lint warns when a function has multiple parameters of the same type that
are passed positionally without named arguments. This helps prevent argument
order mistakes at call sites by encouraging explicit naming.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 9 |

## Test Structure

### Unnamed Duplicate Typed Args Warning

#### functions with duplicate typed params

- ✅ warns on positional call with two text params
- ✅ accepts named arguments without warning
- ✅ works with mixed named and positional args
#### no warning cases

- ✅ does not warn on single parameter
- ✅ does not warn on different typed params
- ✅ does not warn when all params are named
#### real world examples

- ✅ copy function with named args
- ✅ compare function with named args
- ✅ move function with named args

