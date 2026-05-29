# Advanced Indexing and Slicing Specification

**Feature ID:** #1015, #1016, #1017 | **Category:** Language, Collections | **Status:** Complete

_Source: `test/feature/usage/advanced_indexing_spec.spl`_

---

use std.text.{NL}

Tests for advanced indexing features including:
- Negative indexing (Python-style -1, -2, etc.)
- Slice operations with start:end:step syntax
- String slicing
- Multi-dimensional indexing

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 21 |

## Test Structure

### Advanced Indexing

#### negative indexing

- ✅ accesses last element with -1
- ✅ accesses second-to-last with -2
- ✅ accesses first element with negative index
- ✅ works with strings
- ✅ negative indexing with single element
#### slicing operations

- ✅ slices with start and end
- ✅ slices from beginning
- ✅ slices to end
- ✅ slices with step
- ✅ reverses with negative step
- ✅ slices with start:end:step
- ✅ empty slice
#### string slicing

- ✅ slices substring
- ✅ slices from end
- ✅ slices middle
- ✅ reverses string
- ✅ handles UTF-8 characters
#### combined operations

- ✅ slices with negative start
- ✅ slices with negative end
- ✅ slices with both negative
- ✅ negative indices in string slice

