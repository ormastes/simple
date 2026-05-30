# Inline Helpers - Phase 2 Workaround Demo

**Feature ID:** #STDLIB-003 | **Category:** Standard Library | **Status:** Active

_Source: `test/feature/lib/std/helpers_example_spec.spl`_

---

## Overview

Demonstrates the Phase 2 workaround pattern for using standard library helper functions
when the runtime import system has limitations. Tests inline implementations of string
operations (trim, split) and array operations (append_all, partition, flatten) that mirror
the std.text and std.array APIs. Includes real-world usage examples for CSV parsing,
multi-source data combination, and text line processing.

## Syntax

```simple
val trimmed = string_trim_inline("  hello world  ")
expect(trimmed).to_equal("hello world")

val parts = string_split_inline("apple,banana,cherry", ",")
expect(parts.len()).to_equal(3)

val flat_result = array_flatten_inline([[1, 2], [3, 4], [5, 6]])
expect(flat_result.len()).to_equal(6)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 13 |

## Test Structure

### Inline Helpers - Phase 2 Workaround

#### String operations

- ✅ trims whitespace from both ends
- ✅ trims tabs and newlines
- ✅ handles empty string
- ✅ splits string by delimiter
- ✅ splits with multi-character delimiter
- ✅ handles no delimiters found
#### Array operations

- ✅ appends two arrays
- ✅ partitions by predicate
- ✅ flattens nested arrays
- ✅ flattens arrays with different lengths
#### Real-world usage

- ✅ processes CSV data
- ✅ combines data from multiple sources
- ✅ filters and processes text lines

