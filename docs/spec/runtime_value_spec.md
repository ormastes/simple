# RuntimeValue

*Source: `simple/std_lib/test/features/infrastructure/runtime_value_spec.spl`*

---

# RuntimeValue

**Feature ID:** #6
**Category:** Infrastructure
**Difficulty:** Level 3/5
**Status:** Complete
**Implementation:** Rust

## Overview

Tagged pointer value system with 64-bit encoding. Supports integers (61-bit), floats,
booleans, nil, strings, arrays, dicts, and heap objects with type tagging.

## Syntax

Values are automatically tagged during runtime:
- Integers: 61-bit signed (TAG_INT)
- Floats: IEEE 754 NaN-boxed (TAG_FLOAT)
- Booleans/Nil: Special constants (TAG_SPECIAL)
- Heap objects: Strings, Arrays, Dicts, Tuples, Structs (TAG_HEAP)

## Implementation

**Files:**
- src/runtime/src/value/core.rs - Core value types and tagging
- src/runtime/src/value/tags.rs - Tag definitions and encoding
- src/runtime/src/value/collections.rs - Collection implementations

**Tests:**
- src/driver/tests/runner_tests.rs

**Dependencies:** None
**Required By:** Feature #7

## Notes

Uses NaN-boxing for floats. Heap objects share common header. FFI bridge for compiled
code interop.
