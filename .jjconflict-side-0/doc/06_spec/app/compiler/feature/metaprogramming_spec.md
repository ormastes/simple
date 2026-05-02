# Simple Language Metaprogramming - Test Specification

**Feature ID:** Various | **Category:** Language Features | **Status:** Partial Implementation

_Source: `test/feature/usage/metaprogramming_spec.spl`_

---

## Overview

This file contains executable test cases for metaprogramming features that are
currently implemented in Simple's runtime.

Tests cover: comprehensions, indexing, pattern matching, and basic error handling.

**Note:** Advanced features (DSL blocks, decorators, slicing, context managers, move closures)
are not yet fully implemented.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 8 |

## Test Structure

### Metaprogramming Spec

- ✅ list comprehensions
- ✅ list comprehensions - transformation
- ✅ array indexing - basic
- ✅ array indexing - last element
- ✅ pattern matching - guard patterns
- ✅ pattern matching - simple matching
- ✅ error handling - safe division
- ✅ error handling - option pattern

