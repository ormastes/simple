# WASM Compilation Integration

**Feature ID:** #WASM-001 | **Category:** Compiler | **Status:** Active

_Source: `test/feature/usage/wasm_compile_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 36 |

## Test Structure

### WASM Compilation Pipeline

#### Backend Selection for WASM targets

- ✅ selects Wasm backend for wasm32 debug
- ✅ selects Wasm backend for wasm32 release
- ✅ selects Wasm backend for wasm64
- ✅ does not select Wasm backend for x86_64
#### WasmBackend creation

- ✅ creates browser backend
- ✅ creates wasi backend
- ✅ creates minimal backend
- ✅ browser backend needs JS glue
- ✅ wasi backend needs WASI imports
- ✅ minimal backend needs neither
#### WasmTarget properties

- ✅ browser target text
- ✅ wasi target text
- ✅ minimal target text
#### CodegenTarget WASM properties

- ✅ wasm32 is 32-bit
- ✅ wasm32 is wasm
- ✅ wasm64 is wasm
- ✅ wasm32 is not 64-bit
- ✅ x86_64 is not wasm
#### WasmTypeMapper for WASM compilation

- ✅ maps Simple i64 to wasm i64
- ✅ maps Simple bool to wasm i32
- ✅ maps Simple f64 to wasm f64
- ✅ reports i64 size as 8 bytes
- ✅ reports bool size as 1 byte
- ✅ reports unit size as 0 bytes
#### WAT generation (WatBuilder)

- ✅ generates valid WAT module structure
- ✅ generates function with params and result
- ✅ generates complete module with function
#### JavaScript glue generation

- ✅ generates JS glue with WebAssembly loader
- ✅ includes browser bindings
- ✅ includes string decoder
#### BrowserBinding

- ✅ creates console.log binding
- ✅ creates alert binding
- ✅ converts to WasmImport
#### WasmCompileResult

- ✅ creates result with WAT text
- ✅ reports no JS glue when absent
- ✅ reports JS glue when present

