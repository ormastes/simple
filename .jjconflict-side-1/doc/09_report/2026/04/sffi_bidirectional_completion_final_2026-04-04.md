# SFFI Bidirectional Interop — Completion Report

**Date:** 2026-04-04
**Status:** Complete
**Plan:** doc/03_plan/sffi_bidirectional_multi_agent_completion_plan_2026-04-04.md

## Summary

Bidirectional C/C++ SFFI interop is complete. Both directions (Simple to C/C++ and C/C++ to Simple) are supported with explicit contracts, ABI verification, and end-to-end proof tests.

## Workstream Results

| WS | Deliverable | Status |
|----|------------|--------|
| 1 | Interop support matrix | Complete -- doc/06_spec/app/compiler/sffi_interop_support_matrix.md |
| 2 | Error conversion (Result to spl_error_t) | Complete -- error_conversion.spl + header updates |
| 3 | Class-level import (Direction B) | Complete -- PluginClassEntry in manifest + dynamic dispatch |
| 4 | Runtime layout verification | Complete -- spl_verify_layouts() + compute_layout_verification() |
| 5 | Callbacks + exception boundary | Complete -- callback_trampoline.spl + noexcept + SFFI006 |
| 6 | Generator determinism | Complete -- already implemented (validated) |
| 7 | Cross-language proof suite | Complete -- 5 round-trip specs + 3 C/C++ fixtures |
| 8 | Public documentation | Complete -- this report + guide update |

## Key Files

### New files created:
- src/compiler/70.backend/backend/error_conversion.spl
- src/compiler/70.backend/backend/callback_trampoline.spl
- test/unit/compiler/types/runtime_layout_verification_spec.spl
- test/unit/compiler/backend/callback_trampoline_spec.spl
- test/unit/app/plugin/class_import_spec.spl
- test/integration/sffi/callback_roundtrip_spec.spl
- test/integration/sffi/layout_verification_roundtrip_spec.spl
- doc/06_spec/app/compiler/sffi_interop_support_matrix.md

### Key files modified:
- src/compiler/70.backend/backend/c_backend_translate.spl (error conversion, callbacks, layout verification)
- src/compiler/90.tools/header_gen/c_header.spl (error types, callbacks, layout declaration)
- src/compiler/90.tools/header_gen/cpp_header.spl (error throwing, noexcept, callbacks)
- src/compiler/35.semantics/lint/sffi_lint.spl (SFFI001 updated, SFFI006 added)
- src/compiler/30.types/type_layout.spl (compute_layout_verification)
- src/compiler_rust/compiler/src/plugin_manifest.rs (PluginClassEntry)
- src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs (class dispatch)
- src/app/plugin/registry.spl (class-level manifest parsing)

## Completion Criteria Verification

1. Direction A and B both explicitly supported
2. ABI, layout, ownership, error semantics documented and enforced
3. Header/wrapper generation is authoritative (deterministic, validated)
4. Runtime registration/loading works in compiled mode
5. Layout verification generated and tested (compile-time + runtime)
6. Cross-language round-trip examples pass
7. Docs describe bounded, proven interop surface
