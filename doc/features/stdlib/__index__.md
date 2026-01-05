# Standard Library Features

**Category:** Stdlib
**Feature Range:** #200-#204
**Total Specs:** 5
**Total Tests:** 75

Standard library improvements including JSON parsing/serialization, file I/O, string methods, symbol table, and error handling.

## Features

| ID | Feature | Tests | Status |
|----|---------|-------|--------|
| #200 | [JSON Library](200_json_library.md) | 15 | Complete |
| #201 | [File I/O API](201_file_io_api.md) | 11 | Complete |
| #202 | [Symbol Table Cross-Refs](202_symbol_table.md) | 18 | Complete |
| #203 | [Enhanced String Methods](203_string_methods.md) | 20 | Complete |
| #204 | [Try Operator (?)](204_try_operator.md) | 11 | Complete |

## Overview

### JSON Library (#200)
Full JSON library with parsing, serialization, and builder API. Supports JsonValue enum, recursive descent parser, and pretty-printing. Pure Simple implementation used by MCP protocol.

### File I/O API (#201)
Comprehensive file I/O with native functions for reading, writing, and file metadata. Supports sync and async operations, memory-mapped files, and Result-based error handling.

### Symbol Table Cross-Refs (#202)
Full symbol table with cross-reference support for code navigation. Includes RefKind enum, SourceLocation, Reference, QualifiedSymbol classes, and query methods for finding references, implementations, callers, and inheritance chains.

### Enhanced String Methods (#203)
Comprehensive string methods including substring, find, replace, trim, case conversion, split, and more. Over 30 string methods for complete text manipulation.

### Try Operator (#204)
The `?` operator for Result/Option propagation. Unwraps Ok(value)/Some(value) or early-returns Err(e)/None. Familiar syntax for Rust developers.

## Spec Test Location

```
simple/std_lib/test/features/stdlib/
├── json_spec.spl           # #200 JSON Library
├── file_io_spec.spl        # #201 File I/O API
├── symbol_table_spec.spl   # #202 Symbol Table
├── string_methods_spec.spl # #203 String Methods
└── try_operator_spec.spl   # #204 Try Operator
```

## Running Tests

```bash
# Run all stdlib specs
for f in simple/std_lib/test/features/stdlib/*_spec.spl; do
    ./target/release/simple "$f"
done

# Run specific spec
./target/release/simple simple/std_lib/test/features/stdlib/json_spec.spl
```
