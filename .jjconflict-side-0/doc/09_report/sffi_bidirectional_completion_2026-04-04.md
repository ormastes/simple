# SFFI Bidirectional Interop Completion Report

**Date:** 2026-04-04  
**Plan:** [doc/03_plan/sffi_bidirectional_multi_agent_completion_plan_2026-04-04.md](../03_plan/sffi_bidirectional_multi_agent_completion_plan_2026-04-04.md)  
**Support Matrix:** [doc/04_architecture/sffi_bidirectional_support_matrix.md](../04_architecture/sffi_bidirectional_support_matrix.md)  
**Design:** [doc/05_design/sffi_bidirectional_interop.md](../05_design/sffi_bidirectional_interop.md)

## Summary

SFFI bidirectional interop moves from **Partial (advancing)** to **Implemented**.

The compiler now provides:
- Direction A: Simple exports to C and C++ via `.so` generation and header generation
- Direction B: C/C++ imports into Simple via `extern fn` and class-level plugin imports
- Callback trampolines in both directions with `noexcept` exception boundaries
- ABI layout verification at compile-time and runtime
- SFFI006 lint rule enforcing callback safety contracts
- End-to-end round-trip proof tests that compile, link, and execute across the language boundary

## Implementation

### Phase 1: Interop Support Matrix (doc)
- Created `doc/06_spec/app/compiler/sffi_interop_support_matrix.md` -- authoritative contract
- Enumerates all supported directions, ABI guarantees, ownership semantics

### Phase 2: Error Conversion (Direction A)
- Created `src/compiler/70.backend/backend/error_conversion.spl` (414 lines)
- Converts Simple `Result<T, E>` to C-compatible `spl_error_t` struct at the FFI boundary
- Generates error conversion prologue/epilogue in exported functions

### Phase 3: Class-Level Plugin Imports (Direction B)
- Added `PluginClassEntry` to plugin manifest (`plugin_manifest.rs`)
- Class-level dynamic dispatch in `dynamic_ffi.rs`
- Manifest parsing in `src/app/plugin/registry.spl`

### Phase 4: Runtime Layout Verification
- Added `compute_layout_verification()` to `src/compiler/30.types/type_layout.spl`
- Generated `spl_verify_layouts()` function in C headers for compile-time + runtime struct layout checks
- Ensures ABI compatibility between Simple and C/C++ struct definitions

### Phase 5: Callback Trampolines
- Created `src/compiler/70.backend/backend/callback_trampoline.spl` (307 lines)
- Bidirectional callback wrapping: Simple closures callable from C, C function pointers callable from Simple
- `noexcept` exception boundaries prevent unwinding across the FFI boundary

### Phase 6: Generator Determinism Validation
- Validated that C/C++ header generation is deterministic (same input produces identical output)
- Already implemented; verified through round-trip proof tests

### Phase 7: Cross-Language Proof Suite
- Created 5 round-trip integration specs and 1 system-level spec
- Proof tests compile `.so`, generate headers, invoke `gcc`/`g++`, link, and execute real binaries
- Fixtures: `calculator.spl`, `test_calculator.c`, `test_calculator.cpp`

### Phase 8: Documentation + SFFI006 Lint
- Added SFFI006 lint rule to `src/compiler/35.semantics/lint/sffi_lint.spl` (613 lines)
- Enforces callback safety contracts (no captured mutable state across FFI boundary)
- Updated C/C++ header generators with error types, callback typedefs, layout declarations

## Files Changed

### Created (8+)
| File | Lines | Purpose |
|------|-------|---------|
| `src/compiler/70.backend/backend/error_conversion.spl` | 414 | Result-to-spl_error_t conversion |
| `src/compiler/70.backend/backend/callback_trampoline.spl` | 307 | Bidirectional callback wrapping |
| `test/system/sffi_bidirectional_interop_spec.spl` | 15 it | System-level interop spec |
| `test/integration/sffi/direction_a_c_roundtrip_spec.spl` | -- | Simple-to-C round-trip proof |
| `test/integration/sffi/direction_a_cpp_roundtrip_spec.spl` | -- | Simple-to-C++ round-trip proof |
| `test/integration/sffi/direction_b_import_roundtrip_spec.spl` | -- | C-to-Simple import proof |
| `test/integration/sffi/callback_roundtrip_spec.spl` | -- | Callback trampoline proof |
| `test/integration/sffi/layout_verification_roundtrip_spec.spl` | -- | ABI layout verification proof |
| `test/integration/sffi/fixtures/calculator.spl` | -- | Simple library fixture |
| `test/integration/sffi/fixtures/test_calculator.c` | -- | C test fixture |
| `test/integration/sffi/fixtures/test_calculator.cpp` | -- | C++ test fixture |
| `doc/06_spec/app/compiler/sffi_interop_support_matrix.md` | -- | Spec-level support matrix |

### Modified (8)
| File | Change |
|------|--------|
| `src/compiler/70.backend/backend/c_backend_translate.spl` | Error conversion, callbacks, layout verification codegen |
| `src/compiler/90.tools/header_gen/c_header.spl` (469 lines) | Error types, callback typedefs, layout declarations |
| `src/compiler/90.tools/header_gen/cpp_header.spl` | Error throwing, noexcept, namespace mapping, callbacks |
| `src/compiler/35.semantics/lint/sffi_lint.spl` (613 lines) | SFFI001 updated, SFFI006 added |
| `src/compiler/30.types/type_layout.spl` | `compute_layout_verification()` |
| `src/compiler_rust/compiler/src/plugin_manifest.rs` | `PluginClassEntry` |
| `src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs` | Class-level dispatch |
| `src/app/plugin/registry.spl` | Class-level manifest parsing |

### Tests Delivered (6 specs)
| File | Coverage |
|------|----------|
| `test/system/sffi_bidirectional_interop_spec.spl` | 15 it blocks, full feature coverage |
| `test/integration/sffi/direction_a_c_roundtrip_spec.spl` | Compile .so, gen header, gcc, link, execute |
| `test/integration/sffi/direction_a_cpp_roundtrip_spec.spl` | Compile .so, gen C++ header, g++, link, execute |
| `test/integration/sffi/direction_b_import_roundtrip_spec.spl` | extern fn import, plugin manifest, execute |
| `test/integration/sffi/callback_roundtrip_spec.spl` | Bidirectional callback trampoline proof |
| `test/integration/sffi/layout_verification_roundtrip_spec.spl` | ABI layout compile-time + runtime check |

## Verification Evidence

- **Zero `pass_todo`:** No stub markers remain in any SFFI implementation file
- **Zero stubs:** All functions contain real logic, not placeholder implementations
- **Round-trip proofs:** Integration tests compile `.so` shared libraries, generate C/C++ headers, invoke `gcc`/`g++` to compile test harnesses, link against the shared library, and execute the resulting binary
- **SFFI006 lint:** Statically enforces callback safety contracts

## Qualification

- Round-trip proof tests require **compiled mode** (interpreter mode only verifies file loading)
- Round-trip proof tests require a **C/C++ compiler on the host** (`gcc`/`g++` or `clang`/`clang++`)
- Layout verification assumes the **same target ABI** between Simple compiler output and the host C compiler

## Status Promotion

| Metric | Before | After |
|--------|--------|-------|
| Feature status | Partial (advancing) | **Implemented** |
| Direction A (Simple to C) | Partial | **Complete** |
| Direction A (Simple to C++) | Partial | **Complete** |
| Direction B (C to Simple) | Partial | **Complete** |
| Direction B (C++ to Simple) | Not started | **Complete** |
| Callback trampolines | Not started | **Complete** |
| ABI layout verification | Not started | **Complete** |
| SFFI006 lint | Not started | **Complete** |
| Round-trip proof tests | 0 | **6 specs** |

## Known Limitations

- Dynamic loading of C++ templates is deferred (requires C++ ABI mangling)
- Rust FFI direction is deferred (separate feature track)
- Async callback trampolines are not yet supported (sync only)
- Plugin hot-reload does not re-verify layout after reload
