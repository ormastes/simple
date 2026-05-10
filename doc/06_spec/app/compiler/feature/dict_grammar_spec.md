# Dictionary Grammar and Syntax Specification

**Feature ID:** #1002, #1018 | **Category:** Language, Syntax | **Status:** Complete

_Source: `test/feature/usage/dict_grammar_spec.spl`_

---

use std.text.{NL}

Tests for dictionary literal syntax, ensuring correct grammar is used.
Verifies that {"key": value} syntax works correctly.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 18 |

## Test Structure

### Dictionary Grammar

#### basic dict syntax

- ✅ creates dict with string keys
- ✅ creates dict with integer values
- ✅ creates dict with mixed value types
- ✅ creates nested dicts
- ✅ creates empty dict
#### dict with arrays

- ✅ stores arrays as values
- ✅ stores nested structures
#### dict operations

- ✅ inserts new key-value pair
- ✅ updates existing value
- ✅ checks key existence
- ✅ gets keys
- ✅ gets values
#### dict with optional chaining

- ✅ stores optional values
- ✅ uses optional chaining with dict access
- ✅ returns None for missing key with ?
#### dict type annotations

- ✅ annotates string to int dict
- ✅ annotates string to string dict
- ✅ annotates complex value types

