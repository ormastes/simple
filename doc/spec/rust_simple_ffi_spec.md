*Source: `/home/ormastes/dev/pub/simple/test/system/features/ffi/rust_simple_ffi_spec.spl`*
*Last Updated: 2026-01-21*

---

# Rust-to-Simple FFI Specification

**Feature IDs:** #FFI-001 - #FFI-050
**Category:** Runtime
**Difficulty:** 4/5
**Status:** Implemented

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

## Core Value Operations

    RuntimeValue is the fundamental type for FFI communication.
    These functions create and extract values from RuntimeValue.

## Array Operations

    Arrays are heap-allocated collections accessible through FFI.

## Dictionary Operations

    Dictionaries (hash maps) are heap-allocated key-value stores.

## String Operations

    Strings are heap-allocated UTF-8 sequences.

## Math Operations

    Trigonometric, logarithmic, and power functions implemented in Rust.

## Environment Variable Operations

    Access to system environment variables through FFI.

## Runtime Configuration

    Global runtime settings accessible through FFI.

## Type Tag Operations

    RuntimeValue includes a 3-bit type tag for runtime type checking.

## Error Handling

    FFI functions report errors through RuntimeValue or panic bridge.
