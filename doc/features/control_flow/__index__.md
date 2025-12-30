# Control Flow Features (#13, #35, #90-#91)

Control flow constructs and pattern matching.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #13 | [Loops](0013_loops.md) | 2 | Complete | Rust |
| #35 | [Error Handling](0035_error_handling.md) | 3 | Complete | Rust |
| #90 | [Match Expressions](0090_match_expressions.md) | 5 | Complete | Rust |
| #91 | [Conditionals](0091_conditionals.md) | 1 | Complete | Rust |

## Summary

**Status:** 4/4 Complete (100%)

## Test Locations

- **Simple Tests:** `simple/std_lib/test/features/control_flow/`
- **Rust Tests:** `src/driver/tests/interpreter_control.rs`

## Control Constructs

- **Iteration**: for, while, loop with break/continue
- **Branching**: if/elif/else, match
- **Error**: Result-based handling with ? operator
- **Pattern**: Exhaustive matching with guards
