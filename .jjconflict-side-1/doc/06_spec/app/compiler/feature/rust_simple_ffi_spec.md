# Rust-to-Simple FFI Specification

**Feature ID:** #FFI-001 - #FFI-050 | **Category:** Runtime | **Difficulty:** 4/5 | **Status:** Implemented

_Source: `test/feature/usage/rust_simple_ffi_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 32 |

## Test Structure

### FFI Value Operations

#### integer values

- ✅ creates and extracts positive integers
- ✅ creates and extracts negative integers
- ✅ creates and extracts zero
#### float values

- ✅ creates and extracts floats
#### boolean values

- ✅ creates and extracts true
- ✅ creates and extracts false
#### nil values

- ✅ creates nil value
- ✅ non-nil values return false
### FFI Array Operations

#### array creation

- ✅ creates empty array with capacity
#### array manipulation

- ✅ pushes and retrieves elements
- ✅ sets elements at index
- ✅ pops elements
- ✅ clears array
### FFI Dictionary Operations

#### dictionary creation

- ✅ creates empty dictionary
#### dictionary manipulation

- ✅ sets and retrieves values
- ✅ tracks length correctly
### FFI String Operations

- ✅ creates string from literal
- ✅ concatenates two strings
### FFI Math Operations

#### trigonometric functions

- ✅ computes sin(0) equals 0
- ✅ computes cos(0) equals 1
#### power and logarithm

- ✅ computes power
- ✅ computes square root
### FFI Environment Operations

- ✅ gets home directory
- ✅ gets temp directory
- ✅ sets and checks environment variable existence
### FFI Runtime Configuration

- ✅ toggles debug mode
- ✅ toggles macro trace
### FFI Type Tags

- ✅ identifies integer type
- ✅ identifies float type
- ✅ identifies nil/special type
### FFI Error Handling

- ✅ reports function not found
- ✅ reports method not found

