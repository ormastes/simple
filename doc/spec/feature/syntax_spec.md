# Simple Language Syntax Specification - Test Specification

**Feature ID:** #10-19 | **Category:** Language Features | **Status:** Stable

_Source: `test/feature/usage/syntax_spec.spl`_

---

## Overview

Comprehensive tests for Simple's syntax, including literals, string interpolation,
operators, and indentation-based parsing.

Simple uses Python-like indentation with type annotations and explicit execution mode control.

## Related Specifications

- **Types** - Type annotations and type syntax
- **Functions** - Function definition syntax
- **Parser** - Parser implementation details

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### Syntax Spec

- ✅ syntax overview - if/else
- ✅ syntax overview - iteration
- ✅ literals - integer formats
- ✅ literals - floating point
- ✅ literals - typed suffixes
- ✅ string literals - interpolation
- ✅ string literals - raw strings
- ✅ string literals - basic interpolation
- ✅ functional update syntax - arrays
- ✅ functional update syntax - basic
- ✅ functional update syntax - lists
- ✅ functional update syntax - pattern 1
- ✅ functional update syntax - pattern 2
- ✅ parsing design rationale - simplicity
- ✅ parsing design rationale - lambdas

