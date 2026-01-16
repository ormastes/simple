# Interpreter & REPL

*Source: `simple/std_lib/test/features/infrastructure/interpreter_repl_spec.spl`*

---

# Interpreter & REPL

**Feature ID:** #107
**Category:** Infrastructure - Runtime Execution
**Difficulty:** 4/5
**Status:** Complete

## Overview

The Interpreter provides runtime execution of Simple programs without compilation,
supporting full language semantics including async/await, pattern matching, and
associated functions. The REPL (Read-Eval-Print Loop) enables interactive development
and exploration.

## Key Features

- **Full Language Support:** All Simple features work in interpreter
- **Associated Functions:** `Type::method()` calls
- **Async/Await:** Promise-based concurrency
- **Pattern Matching:** Match expressions with exhaustiveness
- **REPL Mode:** Interactive development environment
- **Multi-Mode Execution:** Compare interpreter vs compiler results

## Implementation

**Primary Files:**
- `src/driver/src/interpreter.rs` - Core interpreter (15,876 lines of tests)
- `src/driver/src/cli/repl.rs` - REPL implementation
- `src/driver/src/cli/tui/repl.rs` - TUI REPL interface

**Test Coverage:**
Extensive test suite in `src/driver/tests/interpreter_*.rs`

## Test Coverage

Validates runtime execution and interactive development.

**Given** Simple source code
        **When** interpreting
        **Then** produces correct results

        **Verification:** Interpreter works

**Given** associated function call
        **When** interpreting
        **Then** resolves and calls correctly

        **Example:**
        ```simple
        List.of(1, 2, 3)  # List::of()
        ```

        **Verification:** Associated calls work

**Given** REPL session
        **When** entering expressions
        **Then** evaluates and prints results

        **Example:**
        ```
        > val x = 42
        42
        > x + 1
        43
        ```

        **Verification:** REPL evaluation works

**Given** REPL session
        **When** defining variables
        **Then** persists across evaluations

        **Verification:** State persistence works
