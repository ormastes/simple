# Compiler Import Alias Resolution - System Test Plan

## Request

Cover `FR-COMPILER-002`: same-named imported structs from different modules must resolve through explicit import namespaces, including aliased imports.

## Test

`test/system/compiler_import_alias_resolution_spec.spl`

## Assertions

- `imported_symbol_local_name("CompileOptions", true, "DriverOptions")` returns `DriverOptions`.
- `imported_symbol_local_name("CompileOptions", true, "BackendOptions")` returns `BackendOptions`.
- `imported_symbol_local_name("CompileOptions", false, "")` returns `CompileOptions`.
- The unit resolver SPipe covers the full two-module alias registration path.

## Verification Command

`bin/simple test test/system/compiler_import_alias_resolution_spec.spl`
