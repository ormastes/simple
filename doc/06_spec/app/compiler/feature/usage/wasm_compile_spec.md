# WASM Compilation Integration

End-to-end tests for compiling Simple programs to WebAssembly. Tests backend selection for wasm32/wasm64 targets, WasmBackend creation (browser, WASI, minimal), WasmTypeMapper for type mapping and size calculation, WAT text generation via WatBuilder, JavaScript glue generation with WebAssembly loader and browser bindings, BrowserBinding to WasmImport conversion, and WasmCompileResult structure.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WASM-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/feature/usage/wasm_compile_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

End-to-end tests for compiling Simple programs to WebAssembly. Tests backend
selection for wasm32/wasm64 targets, WasmBackend creation (browser, WASI,
minimal), WasmTypeMapper for type mapping and size calculation, WAT text
generation via WatBuilder, JavaScript glue generation with WebAssembly loader
and browser bindings, BrowserBinding to WasmImport conversion, and
WasmCompileResult structure.

## Syntax

```simple
val backend = WasmBackend__create(WasmTarget.Browser)
val mapper = WasmTypeMapper__create_wasm32()
var builder = WatBuilder__create()
builder.begin_module("test")
```
WASM Compilation Integration Specification

End-to-end tests for compiling Simple programs to WebAssembly.
Tests both LLVM-based and WAT-based compilation paths,
standalone and WASI modes, and backend selection.

Feature IDs: #WASM-COMPILE-001
Category: Compiler Backend
Status: Active

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/wasm_compile/result.json` |

## Scenarios

- selects Wasm backend for wasm32 debug
- selects Wasm backend for wasm32 release
- selects Wasm backend for wasm64
- does not select Wasm backend for x86_64
- creates browser backend
- creates wasi backend
- creates minimal backend
- browser backend needs JS glue
- wasi backend needs WASI imports
- minimal backend needs neither
- browser target text
- wasi target text
- minimal target text
- wasm32 is 32-bit
- wasm32 is wasm
- wasm64 is wasm
- wasm32 is not 64-bit
- x86_64 is not wasm
- maps Simple i64 to wasm i64
- maps Simple bool to wasm i32
- maps Simple f64 to wasm f64
- reports i64 size as 8 bytes
- reports bool size as 1 byte
- reports unit size as 0 bytes
- generates valid WAT module structure
- generates function with params and result
- generates complete module with function
- generates JS glue with WebAssembly loader
- includes browser bindings
- includes string decoder
- creates console.log binding
- creates alert binding
- converts to WasmImport
- creates result with WAT text
- reports no JS glue when absent
- reports JS glue when present
