# GC

*Source: `simple/std_lib/test/features/infrastructure/gc_spec.spl`*

---

# GC

**Feature ID:** #7
**Category:** Infrastructure
**Difficulty:** 3/5
**Status:** Complete

## Overview

Automatic memory management with tracing garbage collection. Handles allocation, collection cycles, and safe deallocation of heap objects.

## Syntax

The GC automatically manages memory for:
- Arrays: `[1, 2, 3]`
- Strings: `"hello world"`
- Dictionaries: `{"key": value}`
- Structs: `MyStruct { field: value }`
- Closures: `|x| x + 1`

No manual memory management required.

## Implementation

**Files:**
- `src/runtime/src/memory/gc.rs`
- `src/runtime/src/memory/mod.rs`

**Test Files:**
- `src/driver/tests/runner_tests.rs`

**Dependencies:** #6 (RuntimeValue)
**Required By:** (none)

## Notes

Abfall-backed GC with optional logging. Supports GC-less mode for real-time contexts. Collection triggered by allocation pressure.
