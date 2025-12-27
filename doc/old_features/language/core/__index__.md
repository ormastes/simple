# Core Language Features (#10-#49)

Fundamental language constructs and types.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #10 | Basic Types | 2 | ✅ | R |
| #11 | Variables | 2 | ✅ | R |
| #12 | Functions | 3 | ✅ | R |
| #13 | Control Flow | 2 | ✅ | R |
| #14 | Structs | 3 | ✅ | R |
| #15 | Classes | 3 | ✅ | R |
| #16 | Enums | 3 | ✅ | R |
| #17 | Pattern Matching | 4 | ✅ | R |
| #18 | GC Memory Management | 5 | ✅ | R |
| #19 | Borrowing | 4 | ✅ | R |
| #20 | Actors | 4 | ✅ | S+R |
| #21 | Async/Await | 4 | ✅ | S+R |
| #22 | Generators | 4 | ✅ | S+R |
| #23 | Futures | 4 | ✅ | S+R |
| #24 | Closures, Macros, String Interpolation | 3 | ✅ | R |

## Summary

**Status:** 15/15 Complete (100%)

## Documentation

- [spec/types.md](../../../spec/types.md) - Type system
- [spec/syntax.md](../../../spec/syntax.md) - Lexical structure
- [spec/functions.md](../../../spec/functions.md) - Functions
- [spec/data_structures.md](../../../spec/data_structures.md) - Structs, classes, enums
- [spec/concurrency.md](../../../spec/concurrency.md) - Actors, async/await

## Test Locations

- **Simple Tests:** `simple/std_lib/test/system/features/language/core/`
- **Rust Tests:** `src/compiler/tests/`, `src/driver/tests/`
