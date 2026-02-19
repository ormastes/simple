# Underscore Wildcard Specification

**Feature ID:** #TBD | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/underscore_wildcard_spec.spl`_

---

## Overview

Tests for underscore (_) as a wildcard placeholder in various contexts:
- Lambda parameters: `\_: expr` to ignore arguments
- For loop patterns: `for _ in items:` to iterate without binding
- Match patterns: `case _:` as a catch-all wildcard

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 7 |

## Test Structure

### Underscore Wildcard Support

### in lambda parameters

- ✅ ignores single argument
- ✅ works in map to transform values
### in for loop patterns

- ✅ iterates without binding
- ✅ uses sum_n_times helper
- ✅ works with list iteration
### in match patterns

- ✅ catches unmatched cases
- ✅ ignores enum payload

