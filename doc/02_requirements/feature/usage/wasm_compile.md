# wasm compile
*Source:* `test/feature/usage/wasm_compile_spec.spl`

## Feature: WASM Compilation Pipeline

### Scenario: Backend Selection for WASM targets

| # | Example | Status |
|---|---------|--------|
| 1 | selects Wasm backend for wasm32 debug | pass |
| 2 | selects Wasm backend for wasm32 release | pass |
| 3 | selects Wasm backend for wasm64 | pass |
| 4 | does not select Wasm backend for x86_64 | pass |

**Example:** selects Wasm backend for wasm32 debug
    Given val kind = select_backend_with_mode(CodegenTarget.Wasm32, BuildMode.Debug, nil)
    Then  expect(kind).to_equal(BackendKind.Wasm)

**Example:** selects Wasm backend for wasm32 release
    Given val kind = select_backend_with_mode(CodegenTarget.Wasm32, BuildMode.Release, nil)
    Then  expect(kind).to_equal(BackendKind.Wasm)

**Example:** selects Wasm backend for wasm64
    Given val kind = select_backend_with_mode(CodegenTarget.Wasm64, BuildMode.Debug, nil)
    Then  expect(kind).to_equal(BackendKind.Wasm)

**Example:** does not select Wasm backend for x86_64
    Given val kind = select_backend_with_mode(CodegenTarget.X86_64, BuildMode.Debug, nil)
    Then  expect(kind).to_equal(BackendKind.Cranelift)

### Scenario: WasmBackend creation

| # | Example | Status |
|---|---------|--------|
| 1 | creates browser backend | pass |
| 2 | creates wasi backend | pass |
| 3 | creates minimal backend | pass |
| 4 | browser backend needs JS glue | pass |
| 5 | wasi backend needs WASI imports | pass |
| 6 | minimal backend needs neither | pass |

**Example:** creates browser backend
    Given val backend = WasmBackend__create(WasmTarget.Browser)
    Then  expect(backend.target.to_text()).to_equal("browser")

**Example:** creates wasi backend
    Given val backend = WasmBackend__create(WasmTarget.Wasi)
    Then  expect(backend.target.to_text()).to_equal("wasi")

**Example:** creates minimal backend
    Given val backend = WasmBackend__create(WasmTarget.Minimal)
    Then  expect(backend.target.to_text()).to_equal("minimal")

**Example:** browser backend needs JS glue
    Given val backend = WasmBackend__create(WasmTarget.Browser)
    Then  expect(backend.target.needs_js_glue()).to_equal(true)

**Example:** wasi backend needs WASI imports
    Given val backend = WasmBackend__create(WasmTarget.Wasi)
    Then  expect(backend.target.needs_wasi_imports()).to_equal(true)

**Example:** minimal backend needs neither
    Given val backend = WasmBackend__create(WasmTarget.Minimal)
    Then  expect(backend.target.needs_js_glue()).to_equal(false)
    Then  expect(backend.target.needs_wasi_imports()).to_equal(false)

### Scenario: WasmTarget properties

| # | Example | Status |
|---|---------|--------|
| 1 | browser target text | pass |
| 2 | wasi target text | pass |
| 3 | minimal target text | pass |

**Example:** browser target text
    Then  expect(WasmTarget.Browser.to_text()).to_equal("browser")

**Example:** wasi target text
    Then  expect(WasmTarget.Wasi.to_text()).to_equal("wasi")

**Example:** minimal target text
    Then  expect(WasmTarget.Minimal.to_text()).to_equal("minimal")

### Scenario: CodegenTarget WASM properties

| # | Example | Status |
|---|---------|--------|
| 1 | wasm32 is 32-bit | pass |
| 2 | wasm32 is wasm | pass |
| 3 | wasm64 is wasm | pass |
| 4 | wasm32 is not 64-bit | pass |
| 5 | x86_64 is not wasm | pass |

**Example:** wasm32 is 32-bit
    Then  expect(CodegenTarget.Wasm32.is_32bit()).to_equal(true)

**Example:** wasm32 is wasm
    Then  expect(CodegenTarget.Wasm32.is_wasm()).to_equal(true)

**Example:** wasm64 is wasm
    Then  expect(CodegenTarget.Wasm64.is_wasm()).to_equal(true)

**Example:** wasm32 is not 64-bit
    Then  expect(CodegenTarget.Wasm32.is_64bit()).to_equal(false)

**Example:** x86_64 is not wasm
    Then  expect(CodegenTarget.X86_64.is_wasm()).to_equal(false)

### Scenario: WasmTypeMapper for WASM compilation

| # | Example | Status |
|---|---------|--------|
| 1 | maps Simple i64 to wasm i64 | pass |
| 2 | maps Simple bool to wasm i32 | pass |
| 3 | maps Simple f64 to wasm f64 | pass |
| 4 | reports i64 size as 8 bytes | pass |
| 5 | reports bool size as 1 byte | pass |
| 6 | reports unit size as 0 bytes | pass |

**Example:** maps Simple i64 to wasm i64
    Given val mapper = WasmTypeMapper__create_wasm32()
    Given val ty = MirType(kind: MirTypeKind.I64)
    Then  expect(mapper.map_type(ty)).to_equal("i64")

**Example:** maps Simple bool to wasm i32
    Given val mapper = WasmTypeMapper__create_wasm32()
    Given val ty = MirType(kind: MirTypeKind.Bool)
    Then  expect(mapper.map_type(ty)).to_equal("i32")

**Example:** maps Simple f64 to wasm f64
    Given val mapper = WasmTypeMapper__create_wasm32()
    Given val ty = MirType(kind: MirTypeKind.F64)
    Then  expect(mapper.map_type(ty)).to_equal("f64")

**Example:** reports i64 size as 8 bytes
    Given val mapper = WasmTypeMapper__create_wasm32()
    Given val ty = MirType(kind: MirTypeKind.I64)
    Then  expect(mapper.size_of(ty)).to_equal(8)

**Example:** reports bool size as 1 byte
    Given val mapper = WasmTypeMapper__create_wasm32()
    Given val ty = MirType(kind: MirTypeKind.Bool)
    Then  expect(mapper.size_of(ty)).to_equal(1)

**Example:** reports unit size as 0 bytes
    Given val mapper = WasmTypeMapper__create_wasm32()
    Given val ty = MirType(kind: MirTypeKind.Unit)
    Then  expect(mapper.size_of(ty)).to_equal(0)

### Scenario: WAT generation (WatBuilder)

| # | Example | Status |
|---|---------|--------|
| 1 | generates valid WAT module structure | pass |
| 2 | generates function with params and result | pass |
| 3 | generates complete module with function | pass |

**Example:** generates valid WAT module structure
    Given var builder = WatBuilder__create()
    Given val wat = builder.build()
    Then  expect(wat).to_contain("(module $test")
    Then  expect(wat).to_contain(")")

**Example:** generates function with params and result
    Given var builder = WatBuilder__create()
    Given val wat = builder.build()
    Then  expect(wat).to_contain("(func $add")
    Then  expect(wat).to_contain("(param i64)")
    Then  expect(wat).to_contain("(result i64)")
    Then  expect(wat).to_contain("i64.add")
    Then  expect(wat).to_contain("return")

**Example:** generates complete module with function
    Given var builder = WatBuilder__create()
    Given val wat = builder.build()
    Then  expect(wat).to_contain("(module $example")
    Then  expect(wat).to_contain("(func $main")
    Then  expect(wat).to_contain("i32.const 0")

### Scenario: JavaScript glue generation

| # | Example | Status |
|---|---------|--------|
| 1 | generates JS glue with WebAssembly loader | pass |
| 2 | includes browser bindings | pass |
| 3 | includes string decoder | pass |

**Example:** generates JS glue with WebAssembly loader
    Given var glue = JsGlueGenerator__create()
    Given val js = glue.generate()
    Then  expect(js).to_contain("WebAssembly")
    Then  expect(js).to_contain("memory")
    Then  expect(js).to_contain("loadWasm")

**Example:** includes browser bindings
    Given var glue = JsGlueGenerator__create()
    Given val js = glue.generate()
    Then  expect(js).to_contain("browser")
    Then  expect(js).to_contain("log")

**Example:** includes string decoder
    Given var glue = JsGlueGenerator__create()
    Given val js = glue.generate()
    Then  expect(js).to_contain("readString")
    Then  expect(js).to_contain("TextDecoder")

### Scenario: BrowserBinding

| # | Example | Status |
|---|---------|--------|
| 1 | creates console.log binding | pass |
| 2 | creates alert binding | pass |
| 3 | converts to WasmImport | pass |

**Example:** creates console.log binding
    Given val binding = BrowserBinding.console_log()
    Then  expect(binding.simple_name).to_equal("print")
    Then  expect(binding.js_module).to_equal("console")
    Then  expect(binding.js_function).to_equal("log")

**Example:** creates alert binding
    Given val binding = BrowserBinding.alert()
    Then  expect(binding.simple_name).to_equal("alert")
    Then  expect(binding.js_module).to_equal("window")
    Then  expect(binding.js_function).to_equal("alert")

**Example:** converts to WasmImport
    Given val binding = BrowserBinding.console_log()
    Given val import_def = binding.to_import()
    Then  expect(import_def.module_name).to_equal("browser")
    Then  expect(import_def.field_name).to_equal("log")

### Scenario: WasmCompileResult

| # | Example | Status |
|---|---------|--------|
| 1 | creates result with WAT text | pass |
| 2 | reports no JS glue when absent | pass |
| 3 | reports JS glue when present | pass |

**Example:** creates result with WAT text
    Given val result = WasmCompileResult(
    Then  expect(result.module_name).to_equal("test")
    Then  expect(result.wat).to_contain("module")

**Example:** reports no JS glue when absent
    Given val result = WasmCompileResult(
    Then  expect(result.has_js_glue()).to_equal(false)

**Example:** reports JS glue when present
    Given val result = WasmCompileResult(
    Then  expect(result.has_js_glue()).to_equal(true)


