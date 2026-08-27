# WASM Compilation Integration

> End-to-end tests for compiling Simple programs to WebAssembly. Tests backend selection for wasm32/wasm64 targets, WasmBackend creation (browser, WASI, minimal), WasmTypeMapper for type mapping and size calculation, WAT text generation via WatBuilder, JavaScript glue generation with WebAssembly loader and browser bindings, BrowserBinding to WasmImport conversion, and WasmCompileResult structure.

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
| Source | `test/feature/usage/wasm_compile_spec.spl` |
| Updated | 2026-08-26 |
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
use std.spec.step

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

- env_skip: WASM not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env_skip: WASM not available")
val reason = test_env_gate_skip("SIMPLE_WASM_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### Backend Selection for WASM targets

#### selects Wasm backend for wasm32 debug

- selects Wasm backend for wasm32 debug
   - Expected: kind equals `BackendKind.Wasm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects Wasm backend for wasm32 debug")
val kind = select_backend_with_mode(CodegenTarget.Wasm32, BuildMode.Debug, nil)
expect(kind).to_equal(BackendKind.Wasm)
```

</details>

#### selects Wasm backend for wasm32 release

- selects Wasm backend for wasm32 release
   - Expected: kind equals `BackendKind.Wasm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects Wasm backend for wasm32 release")
val kind = select_backend_with_mode(CodegenTarget.Wasm32, BuildMode.Release, nil)
expect(kind).to_equal(BackendKind.Wasm)
```

</details>

#### selects Wasm backend for wasm64

- selects Wasm backend for wasm64
   - Expected: kind equals `BackendKind.Wasm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("selects Wasm backend for wasm64")
val kind = select_backend_with_mode(CodegenTarget.Wasm64, BuildMode.Debug, nil)
expect(kind).to_equal(BackendKind.Wasm)
```

</details>

#### does not select Wasm backend for x86_64

- does not select Wasm backend for x86_64
   - Expected: kind equals `BackendKind.Cranelift`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not select Wasm backend for x86_64")
val kind = select_backend_with_mode(CodegenTarget.X86_64, BuildMode.Debug, nil)
expect(kind).to_equal(BackendKind.Cranelift)
```

</details>

#### WasmBackend creation

#### creates browser backend

- creates browser backend
   - Expected: backend.target.to_text() equals `browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates browser backend")
val backend = WasmBackend__create(WasmTarget.Browser)
expect(backend.target.to_text()).to_equal("browser")
```

</details>

#### creates wasi backend

- creates wasi backend
   - Expected: backend.target.to_text() equals `wasi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates wasi backend")
val backend = WasmBackend__create(WasmTarget.Wasi)
expect(backend.target.to_text()).to_equal("wasi")
```

</details>

#### creates minimal backend

- creates minimal backend
   - Expected: backend.target.to_text() equals `minimal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates minimal backend")
val backend = WasmBackend__create(WasmTarget.Minimal)
expect(backend.target.to_text()).to_equal("minimal")
```

</details>

#### browser backend needs JS glue

- browser backend needs JS glue
   - Expected: backend.target.needs_js_glue() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("browser backend needs JS glue")
val backend = WasmBackend__create(WasmTarget.Browser)
expect(backend.target.needs_js_glue()).to_equal(true)
```

</details>

#### wasi backend needs WASI imports

- wasi backend needs WASI imports
   - Expected: backend.target.needs_wasi_imports() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wasi backend needs WASI imports")
val backend = WasmBackend__create(WasmTarget.Wasi)
expect(backend.target.needs_wasi_imports()).to_equal(true)
```

</details>

#### minimal backend needs neither

- minimal backend needs neither
   - Expected: backend.target.needs_js_glue() is false
   - Expected: backend.target.needs_wasi_imports() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("minimal backend needs neither")
val backend = WasmBackend__create(WasmTarget.Minimal)
expect(backend.target.needs_js_glue()).to_equal(false)
expect(backend.target.needs_wasi_imports()).to_equal(false)
```

</details>

#### WasmTarget properties

#### browser target text

- browser target text
   - Expected: WasmTarget.Browser.to_text() equals `browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("browser target text")
expect(WasmTarget.Browser.to_text()).to_equal("browser")
```

</details>

#### wasi target text

- wasi target text
   - Expected: WasmTarget.Wasi.to_text() equals `wasi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wasi target text")
expect(WasmTarget.Wasi.to_text()).to_equal("wasi")
```

</details>

#### minimal target text

- minimal target text
   - Expected: WasmTarget.Minimal.to_text() equals `minimal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("minimal target text")
expect(WasmTarget.Minimal.to_text()).to_equal("minimal")
```

</details>

#### CodegenTarget WASM properties

#### wasm32 is 32-bit

- wasm32 is 32-bit
   - Expected: CodegenTarget.Wasm32.is_32bit() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wasm32 is 32-bit")
expect(CodegenTarget.Wasm32.is_32bit()).to_equal(true)
```

</details>

#### wasm32 is wasm

- wasm32 is wasm
   - Expected: CodegenTarget.Wasm32.is_wasm() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wasm32 is wasm")
expect(CodegenTarget.Wasm32.is_wasm()).to_equal(true)
```

</details>

#### wasm64 is wasm

- wasm64 is wasm
   - Expected: CodegenTarget.Wasm64.is_wasm() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wasm64 is wasm")
expect(CodegenTarget.Wasm64.is_wasm()).to_equal(true)
```

</details>

#### wasm32 is not 64-bit

- wasm32 is not 64-bit
   - Expected: CodegenTarget.Wasm32.is_64bit() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("wasm32 is not 64-bit")
expect(CodegenTarget.Wasm32.is_64bit()).to_equal(false)
```

</details>

#### x86_64 is not wasm

- x86_64 is not wasm
   - Expected: CodegenTarget.X86_64.is_wasm() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("x86_64 is not wasm")
expect(CodegenTarget.X86_64.is_wasm()).to_equal(false)
```

</details>

#### WasmTypeMapper for WASM compilation

#### maps Simple i64 to wasm i64

- maps Simple i64 to wasm i64
   - Expected: mapper.map_type(ty) equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maps Simple i64 to wasm i64")
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.I64)
expect(mapper.map_type(ty)).to_equal("i64")
```

</details>

#### maps Simple bool to wasm i32

- maps Simple bool to wasm i32
   - Expected: mapper.map_type(ty) equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maps Simple bool to wasm i32")
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.Bool)
expect(mapper.map_type(ty)).to_equal("i32")
```

</details>

#### maps Simple f64 to wasm f64

- maps Simple f64 to wasm f64
   - Expected: mapper.map_type(ty) equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maps Simple f64 to wasm f64")
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.F64)
expect(mapper.map_type(ty)).to_equal("f64")
```

</details>

#### reports i64 size as 8 bytes

- reports i64 size as 8 bytes
   - Expected: mapper.size_of(ty) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports i64 size as 8 bytes")
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.I64)
expect(mapper.size_of(ty)).to_equal(8)
```

</details>

#### reports bool size as 1 byte

- reports bool size as 1 byte
   - Expected: mapper.size_of(ty) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports bool size as 1 byte")
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.Bool)
expect(mapper.size_of(ty)).to_equal(1)
```

</details>

#### reports unit size as 0 bytes

- reports unit size as 0 bytes
   - Expected: mapper.size_of(ty) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports unit size as 0 bytes")
val mapper = WasmTypeMapper__create_wasm32()
val ty = MirType(kind: MirTypeKind.Unit)
expect(mapper.size_of(ty)).to_equal(0)
```

</details>

#### WAT generation (WatBuilder)

#### generates valid WAT module structure

- generates valid WAT module structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates valid WAT module structure")
var builder = WatBuilder__create()
builder.begin_module("test")
builder.end_module()
val wat = builder.build()
expect(wat).to_contain("(module $test")
expect(wat).to_contain(")")
```

</details>

#### generates function with params and result

- generates function with params and result


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates function with params and result")
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

- generates complete module with function


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates complete module with function")
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

- generates JS glue with WebAssembly loader


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generates JS glue with WebAssembly loader")
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

- includes browser bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes browser bindings")
var glue = JsGlueGenerator__create()
glue.add_binding(BrowserBinding.console_log())
val js = glue.generate()
expect(js).to_contain("browser")
expect(js).to_contain("log")
```

</details>

#### includes string decoder

- includes string decoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("includes string decoder")
var glue = JsGlueGenerator__create()
val js = glue.generate()
expect(js).to_contain("readString")
expect(js).to_contain("TextDecoder")
```

</details>

#### BrowserBinding

#### creates console.log binding

- creates console.log binding
   - Expected: binding.simple_name equals `print`
   - Expected: binding.js_module equals `console`
   - Expected: binding.js_function equals `log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates console.log binding")
val binding = BrowserBinding.console_log()
expect(binding.simple_name).to_equal("print")
expect(binding.js_module).to_equal("console")
expect(binding.js_function).to_equal("log")
```

</details>

#### creates alert binding

- creates alert binding
   - Expected: binding.simple_name equals `alert`
   - Expected: binding.js_module equals `window`
   - Expected: binding.js_function equals `alert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates alert binding")
val binding = BrowserBinding.alert()
expect(binding.simple_name).to_equal("alert")
expect(binding.js_module).to_equal("window")
expect(binding.js_function).to_equal("alert")
```

</details>

#### converts to WasmImport

- converts to WasmImport
   - Expected: import_def.module_name equals `browser`
   - Expected: import_def.field_name equals `log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("converts to WasmImport")
val binding = BrowserBinding.console_log()
val import_def = binding.to_import()
expect(import_def.module_name).to_equal("browser")
expect(import_def.field_name).to_equal("log")
```

</details>

#### WasmCompileResult

#### creates result with WAT text

- creates result with WAT text
   - Expected: result.module_name equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates result with WAT text")
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

- reports no JS glue when absent
   - Expected: result.has_js_glue() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports no JS glue when absent")
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

- reports JS glue when present
   - Expected: result.has_js_glue() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports JS glue when present")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6095d715dd617cfa870a1e84dad5c684a33e43b4f60c0988223b4bf6ae339966`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6095d715dd617cfa870a1e84dad5c684a33e43b4f60c0988223b4bf6ae339966`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6095d715dd617cfa870a1e84dad5c684a33e43b4f60c0988223b4bf6ae339966`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/wasm_compile_spec.spl
mirror: doc/06_spec/feature/usage/wasm_compile_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/wasm_compile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/wasm_compile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/wasm_compile_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/wasm_compile_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: WASM not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/wasm_compile_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects Wasm backend for wasm32 debug' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/wasm_compile_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects Wasm backend for wasm32 release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
