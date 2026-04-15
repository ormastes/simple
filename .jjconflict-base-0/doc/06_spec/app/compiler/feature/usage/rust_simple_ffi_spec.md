# Rust-to-Simple FFI Specification

The Simple language provides a comprehensive Foreign Function Interface (FFI) system that enables bidirectional communication between Rust and Simple code. This specification tests the core FFI functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FFI-001 - #FFI-050 |
| Category | Runtime |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/feature/usage/rust_simple_ffi_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

The Simple language provides a comprehensive Foreign Function Interface (FFI)
system that enables bidirectional communication between Rust and Simple code.
This specification tests the core FFI functionality.

## Key Concepts

| Concept | Description |
|---------|-------------|
| RuntimeValue | 64-bit tagged value (3-bit tag + 61-bit payload) |
| BridgeValue | C-compatible wrapper for complex types |
| Extern Function | Function implemented in Rust, callable from Simple |
| Symbol Registry | Maps function names to Rust function pointers |

## Behavior

- FFI functions use C calling convention (extern C)
- RuntimeValue passed by value (64 bits, no allocation)
- Complex types allocated on heap, pointer stored in RuntimeValue
- Type marshalling handled automatically for primitive types

## Implementation Notes

FFI functions are organized in phases under src/rust/runtime/src/value/ffi/:
- Phase 1: Core value operations
- Phase 2: Hash and concurrent structures
- Phase 3: Interpreter bridge, contracts
- Phase 4-13: Math, file I/O, networking, GPU, etc.

Total: 562+ FFI functions across 50+ modules.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/rust_simple_ffi/result.json` |

## Scenarios

- creates and extracts positive integers
- creates and extracts negative integers
- creates and extracts zero
- creates and extracts floats
- creates and extracts true
- creates and extracts false
- creates nil value
- non-nil values return false
- creates empty array with capacity
- pushes and retrieves elements
- sets elements at index
- pops elements
- clears array
- creates empty dictionary
- sets and retrieves values
- tracks length correctly
- creates string from literal
- concatenates two strings
- computes sin(0) equals 0
- computes cos(0) equals 1
- computes power
- computes square root
- gets home directory
- gets temp directory
- sets and checks environment variable existence
- toggles debug mode
- toggles macro trace
- identifies integer type
- identifies float type
- identifies nil/special type
- reports function not found
- reports method not found
