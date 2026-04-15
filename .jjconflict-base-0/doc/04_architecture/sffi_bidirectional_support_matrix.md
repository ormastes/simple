# SFFI Bidirectional Interop — Support Matrix

**Date:** 2026-04-04
**Feature:** Simple Foreign Function Interface — bidirectional C/C++ interop

## Feature Status: Implemented

## Direction A: Simple → C/C++

| Capability | Status | Key File |
|-----------|--------|----------|
| `@export` attribute on functions | Implemented | `src/compiler/70.backend/backend/error_conversion.spl` |
| Shared library (.so/.dylib/.dll) generation | Implemented | Compiler driver |
| C header generation | Implemented | `src/compiler/90.tools/header_gen/c_header.spl` |
| C++ header generation | Implemented | `src/compiler/90.tools/header_gen/c_header.spl` |
| Namespace mapping (C++) | Implemented | Header gen |
| ABI layout verification | Implemented | Layout checker |
| Round-trip test (compile .so → gen header → compile C consumer → link → execute) | Implemented | `test/integration/sffi/direction_a_c_roundtrip_spec.spl` |
| C++ round-trip | Implemented | `test/integration/sffi/direction_a_cpp_roundtrip_spec.spl` |

## Direction B: C/C++ → Simple

| Capability | Status | Key File |
|-----------|--------|----------|
| `extern fn` import | Implemented | `src/lib/ffi/mod.spl` |
| Class-level plugin imports | Implemented | Compiler frontend |
| Callback trampolines | Implemented | `src/compiler/70.backend/backend/callback_trampoline.spl` |
| Direction B round-trip test | Implemented | `test/integration/sffi/direction_b_import_roundtrip_spec.spl` |
| Callback round-trip test | Implemented | `test/integration/sffi/callback_roundtrip_spec.spl` |

## Quality & Tooling

| Capability | Status |
|-----------|--------|
| SFFI006 lint rule | Implemented |
| Layout verification at build | Implemented |
| Error conversion (Result → C error codes) | Implemented |
| 15-test system spec | Implemented |
| 5 round-trip integration specs | Implemented |

## Deferred

| Capability | Status |
|-----------|--------|
| Dynamic loading of C++ templates | Not planned |
| Rust FFI direction | Not planned |
| WASM FFI | Not planned |

## Test Evidence

All round-trip tests are compiled-mode tests that:
1. Compile Simple code to shared library
2. Generate C/C++ headers
3. Compile C/C++ consumer with gcc/clang
4. Link against the shared library
5. Execute and verify PASS output

Requires: compiled mode + C compiler on host.
