# Macros

*Source: `simple/std_lib/test/features/language/macros_spec.spl`*

---

# Macros

**Feature ID:** #29
**Category:** Language
**Difficulty:** Level 4/5
**Status:** Complete
**Implementation:** Rust

## Overview

Compile-time code generation with builtin and user-defined macros. Includes vec!,
assert!, assert_eq!, format!, panic!, dbg! and custom macro definitions.

## Syntax

**Builtin macros:**
```simple
vec!(1, 2, 3)              # Create array
assert!(condition)         # Runtime assertion
assert_eq!(a, b)          # Equality assertion
format!("hello", " ", x)   # String concatenation
dbg!(expr)                # Debug print and return
panic!(msg)               # Abort execution
```

**User-defined macros:**
```simple
macro double(x: i32) -> (returns result: i32):
    emit result:
        x * 2

val result = double!(21)  # Expands at compile time
```

## Implementation

**Files:**
- src/compiler/src/interpreter_macro.rs - Macro expansion interpreter
- src/parser/src/statements/mod.rs - Macro definition parsing

**Tests:**
- src/driver/tests/interpreter_macros.rs
- src/driver/tests/interpreter_macro_hygiene.rs

**Dependencies:** Features #1, #2, #12
**Required By:** Features #180, #181, #182

## Notes

User macros use emit blocks to specify output. Macro hygiene prevents name collisions.
