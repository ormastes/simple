# Compiler CompileOptions Field Access - Local Research

## Scope

Feature request: `FR-COMPILER-001` in `doc/08_tracking/feature_request/compiler_requests.md`.

## Findings

- The failing fields (`input_files`, `mode`, `low_memory`) belong to `compiler.common.driver_core_types.CompileOptions`.
- `compiler.backend.backend.backend_types` also defines a `CompileOptions` struct, but it has backend-specific fields such as `target`, `opt_level`, and `verify_output`.
- The request investigation already identified the runtime "Function not found" errors as a wrong-struct import-resolution symptom, not missing field declarations.
- `FR-COMPILER-002` added explicit import pre-registration and alias-aware local symbol naming in `src/compiler/20.hir/hir_lowering/items.spl`, which is the implementation path needed for this request.

## Selected Fix

Close `FR-COMPILER-001` by adding system coverage that explicitly imports the driver `CompileOptions` and reads the driver-only fields that previously failed.

## Regression Surface

- System SPipe: `test/system/compiler_compile_options_field_access_spec.spl`
- Related resolver coverage: `test/unit/compiler/hir/resolve_import_symbols_spec.spl`
