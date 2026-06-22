# WASM Compilation Integration

> End-to-end tests for compiling Simple programs to WebAssembly. Tests backend selection for wasm32/wasm64 targets, WasmBackend creation (browser, WASI, minimal), WasmTypeMapper for type mapping and size calculation, WAT text generation via WatBuilder, JavaScript glue generation with WebAssembly loader and browser bindings, BrowserBinding to WasmImport conversion, and WasmCompileResult structure.

<!-- sdn-diagram:id=wasm_compile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_compile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_compile_spec -> compiler
wasm_compile_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_compile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WASM Compilation Integration

End-to-end tests for compiling Simple programs to WebAssembly. Tests backend selection for wasm32/wasm64 targets, WasmBackend creation (browser, WASI, minimal), WasmTypeMapper for type mapping and size calculation, WAT text generation via WatBuilder, JavaScript glue generation with WebAssembly loader and browser bindings, BrowserBinding to WasmImport conversion, and WasmCompileResult structure.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WASM-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/feature/usage/wasm_compile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### WASM Compilation Pipeline

#### env_skip: WASM not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_WASM_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### Backend Selection for WASM targets

#### selects Wasm backend for wasm32 debug

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = select_backend_with_mode(CodegenTarget.Wasm32, BuildMode.Debug, nil)
expect(kind).to_equal(BackendKind.Wasm)
```

</details>

#### selects Wasm backend for wasm32 release

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = select_backend_with_mode(CodegenTarget.Wasm32, BuildMode.Release, nil)
expect(kind).to_equal(BackendKind.Wasm)
```

</details>

#### selects Wasm backend for wasm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = select_backend_with_mode(CodegenTarget.Wasm64, BuildMode.Debug, nil)
expect(kind).to_equal(BackendKind.Wasm)
```

</details>

#### does not select Wasm backend for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = select_backend_with_mode(CodegenTarget.X86_64, BuildMode.Debug, nil)
expect(kind).to_equal(BackendKind.Cranelift)
```

</details>

#### WasmBackend creation

#### creates browser backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend__create(WasmTarget.Browser)
expect(backend.target.to_text()).to_equal("browser")
```

</details>

#### creates wasi backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend__create(WasmTarget.Wasi)
expect(backend.target.to_text()).to_equal("wasi")
```

</details>

#### creates minimal backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend__create(WasmTarget.Minimal)
expect(backend.target.to_text()).to_equal("minimal")
```

</details>

#### browser backend needs JS glue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend__create(WasmTarget.Browser)
expect(backend.target.needs_js_glue()).to_equal(true)
```

</details>

#### wasi backend needs WASI imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend__create(WasmTarget.Wasi)
expect(backend.target.needs_wasi_imports()).to_equal(true)
```

</details>

#### minimal backend needs neither

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend__create(WasmTarget.Minimal)
expect(backend.target.needs_js_glue()).to_equal(false)
expect(backend.target.needs_wasi_imports()).to_equal(false)
```

</details>

#### WasmTarget properties

#### browser target text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WasmTarget.Browser.to_text()).to_equal("browser")
```

</details>

#### wasi target text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WasmTarget.Wasi.to_text()).to_equal("wasi")
```

</details>

#### minimal target text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WasmTarget.Minimal.to_text()).to_equal("minimal")
```

</details>

#### CodegenTarget WASM properties

#### wasm32 is 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CodegenTarget.Wasm32.is_32bit()).to_equal(true)
```

</details>

#### wasm32 is wasm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CodegenTarget.Wasm32.is_wasm()).to_equal(true)
```

</details>

#### wasm64 is wasm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CodegenTarget.Wasm64.is_wasm()).to_equal(true)
```

</details>

#### wasm32 is not 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CodegenTarget.Wasm32.is_64bit()).to_equal(false)
```

</details>

#### x86_64 is not wasm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CodegenTarget.X86_64.is_wasm()).to_equal(false)
```

</details>

#### WasmTypeMapper for WASM compilation

#### maps Simple i64 to wasm i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.I64)
expect(mapper.map_type(ty)).to_equal("i64")
```

</details>

#### maps Simple bool to wasm i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.Bool)
expect(mapper.map_type(ty)).to_equal("i32")
```

</details>

#### maps Simple f64 to wasm f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.F64)
expect(mapper.map_type(ty)).to_equal("f64")
```

</details>

#### reports i64 size as 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.I64)
expect(mapper.size_of(ty)).to_equal(8)
```

</details>

#### reports bool size as 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.Bool)
expect(mapper.size_of(ty)).to_equal(1)
```

</details>

#### reports unit size as 0 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.Unit)
expect(mapper.size_of(ty)).to_equal(0)
```

</details>

#### WAT generation (WatBuilder)

#### generates valid WAT module structure

1. var builder = WatBuilder  create
2. builder begin module
3. builder end module


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder__create()
builder.begin_module("test")
builder.end_module()
val wat = builder.build()
expect(wat).to_contain("(module $test")
expect(wat).to_contain(")")
```

</details>

#### generates function with params and result

1. var builder = WatBuilder  create
2. builder begin func
3. builder emit local get
4. builder emit local get
5. builder emit i64 add
6. builder emit return
7. builder end func


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder__create()
builder.begin_func("add", [WasmType.I64, WasmType.I64], [WasmType.I64])
builder.emit_local_get(0)
builder.emit_local_get(1)
builder.emit_i64_add()
builder.emit_return()
builder.end_func()
val wat = builder.build()
expect(wat).to_contain("(func $add")
expect(wat).to_contain("(param i64)")
expect(wat).to_contain("(result i64)")
expect(wat).to_contain("i64.add")
expect(wat).to_contain("return")
```

</details>

#### generates complete module with function

1. var builder = WatBuilder  create
2. builder begin module
3. builder begin func
4. builder emit i32 const
5. builder emit return
6. builder end func
7. builder end module


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder__create()
builder.begin_module("example")
builder.begin_func("main", [], [WasmType.I32])
builder.emit_i32_const(0)
builder.emit_return()
builder.end_func()
builder.end_module()
val wat = builder.build()
expect(wat).to_contain("(module $example")
expect(wat).to_contain("(func $main")
expect(wat).to_contain("i32.const 0")
```

</details>

#### JavaScript glue generation

#### generates JS glue with WebAssembly loader

1. var glue = JsGlueGenerator  create
2. glue add binding
3. glue add export


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var glue = JsGlueGenerator__create()
glue.add_binding(BrowserBinding.console_log())
glue.add_export("main")
val js = glue.generate()
expect(js).to_contain("WebAssembly")
expect(js).to_contain("memory")
expect(js).to_contain("loadWasm")
```

</details>

#### includes browser bindings

1. var glue = JsGlueGenerator  create
2. glue add binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var glue = JsGlueGenerator__create()
glue.add_binding(BrowserBinding.console_log())
val js = glue.generate()
expect(js).to_contain("browser")
expect(js).to_contain("log")
```

</details>

#### includes string decoder

1. var glue = JsGlueGenerator  create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var glue = JsGlueGenerator__create()
val js = glue.generate()
expect(js).to_contain("readString")
expect(js).to_contain("TextDecoder")
```

</details>

#### BrowserBinding

#### creates console.log binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = BrowserBinding.console_log()
expect(binding.simple_name).to_equal("print")
expect(binding.js_module).to_equal("console")
expect(binding.js_function).to_equal("log")
```

</details>

#### creates alert binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = BrowserBinding.alert()
expect(binding.simple_name).to_equal("alert")
expect(binding.js_module).to_equal("window")
expect(binding.js_function).to_equal("alert")
```

</details>

#### converts to WasmImport

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = BrowserBinding.console_log()
val import_def = binding.to_import()
expect(import_def.module_name).to_equal("browser")
expect(import_def.field_name).to_equal("log")
```

</details>

#### WasmCompileResult

#### creates result with WAT text

1. wat: "
   - Expected: result.module_name equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = WasmCompileResult(
    module_name: "test",
    wat: "(module $test)",
    wasm: nil,
    js_glue: nil,
    compile_time_ms: 0
)
expect(result.module_name).to_equal("test")
expect(result.wat).to_contain("module")
```

</details>

#### reports no JS glue when absent

1. wat: "
   - Expected: result.has_js_glue() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = WasmCompileResult(
    module_name: "test",
    wat: "(module)",
    wasm: nil,
    js_glue: nil,
    compile_time_ms: 0
)
expect(result.has_js_glue()).to_equal(false)
```

</details>

#### reports JS glue when present

1. wat: "
2. js glue: Some
   - Expected: result.has_js_glue() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = WasmCompileResult(
    module_name: "test",
    wat: "(module)",
    wasm: nil,
    js_glue: Some("const x = 1;"),
    compile_time_ms: 0
)
expect(result.has_js_glue()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
