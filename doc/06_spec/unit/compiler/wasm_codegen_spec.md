# wasm_codegen_spec

> Purpose: Prove that WAT Codegen.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wasm_codegen_spec

Purpose: Prove that WAT Codegen.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/wasm_codegen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that WAT Codegen.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### WAT Codegen

#### WatBuilder basics

#### creates empty module

- creates empty module
- Verify: creates empty module


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty module")
step("Verify: creates empty module")
# @req: REQ-COMP-WAT-CODEGEN-001
var builder = WatBuilder.create()
builder.begin_module("test")
builder.end_module()
val wat = builder.build()
expect(wat).to_contain("(module $test")
expect(wat).to_contain(")")
```

</details>

#### emits i32 const

- emits i32 const
- Verify: emits i32 const


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i32 const")
step("Verify: emits i32 const")
var builder = WatBuilder.create()
builder.emit_i32_const(42)
val wat = builder.build()
expect(wat).to_contain("i32.const 42")
```

</details>

#### emits i64 const

- emits i64 const
- Verify: emits i64 const


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i64 const")
step("Verify: emits i64 const")
var builder = WatBuilder.create()
builder.emit_i64_const(100)
val wat = builder.build()
expect(wat).to_contain("i64.const 100")
```

</details>

#### emits f64 const

- emits f64 const
- Verify: emits f64 const


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64 const")
step("Verify: emits f64 const")
var builder = WatBuilder.create()
builder.emit_f64_const(3.14)
val wat = builder.build()
expect(wat).to_contain("f64.const")
```

</details>

#### emits local get and set by name

- emits local get and set by name
- Verify: emits local get and set by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits local get and set by name")
step("Verify: emits local get and set by name")
var builder = WatBuilder.create()
builder.emit_local_named_get("x")
builder.emit_local_named_set("y")
val wat = builder.build()
expect(wat).to_contain("local.get $x")
expect(wat).to_contain("local.set $y")
```

</details>

#### emits call by name

- emits call by name
- Verify: emits call by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits call by name")
step("Verify: emits call by name")
var builder = WatBuilder.create()
builder.emit_call_named("my_func")
val wat = builder.build()
expect(wat).to_contain("call $my_func")
```

</details>

#### WatBuilder control flow

#### emits block and end

- emits block and end
- Verify: emits block and end


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits block and end")
step("Verify: emits block and end")
var builder = WatBuilder.create()
builder.emit_block("exit")
builder.emit_end()
val wat = builder.build()
expect(wat).to_contain("(block $exit")
```

</details>

<details>
<summary>Advanced: emits loop</summary>

#### emits loop

- emits loop
- Verify: emits loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits loop")
step("Verify: emits loop")
var builder = WatBuilder.create()
builder.emit_loop("loop_start")
builder.emit_end()
val wat = builder.build()
expect(wat).to_contain("(loop $loop_start")
```

</details>


</details>

#### emits branch instructions

- emits branch instructions
- Verify: emits branch instructions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits branch instructions")
step("Verify: emits branch instructions")
var builder = WatBuilder.create()
builder.emit_br("target")
builder.emit_br_if("cond_target")
val wat = builder.build()
expect(wat).to_contain("br $target")
expect(wat).to_contain("br_if $cond_target")
```

</details>

#### emits return

- emits return
- Verify: emits return


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits return")
step("Verify: emits return")
var builder = WatBuilder.create()
builder.emit_return()
val wat = builder.build()
expect(wat).to_contain("return")
```

</details>

#### emits unreachable

- emits unreachable
- Verify: emits unreachable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits unreachable")
step("Verify: emits unreachable")
var builder = WatBuilder.create()
builder.emit_unreachable()
val wat = builder.build()
expect(wat).to_contain("unreachable")
```

</details>

#### WatBuilder arithmetic

#### emits i64 arithmetic

- emits i64 arithmetic
- Verify: emits i64 arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i64 arithmetic")
step("Verify: emits i64 arithmetic")
var builder = WatBuilder.create()
builder.emit_i64_add()
builder.emit_i64_sub()
builder.emit_i64_mul()
builder.emit_i64_div_s()
builder.emit_i64_rem_s()
val wat = builder.build()
expect(wat).to_contain("i64.add")
expect(wat).to_contain("i64.sub")
expect(wat).to_contain("i64.mul")
expect(wat).to_contain("i64.div_s")
expect(wat).to_contain("i64.rem_s")
```

</details>

#### emits f64 arithmetic

- emits f64 arithmetic
- Verify: emits f64 arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64 arithmetic")
step("Verify: emits f64 arithmetic")
var builder = WatBuilder.create()
builder.emit_f64_add()
builder.emit_f64_sub()
builder.emit_f64_mul()
builder.emit_f64_div()
val wat = builder.build()
expect(wat).to_contain("f64.add")
expect(wat).to_contain("f64.sub")
expect(wat).to_contain("f64.mul")
expect(wat).to_contain("f64.div")
```

</details>

#### WatBuilder comparison

#### emits i64 comparisons

- emits i64 comparisons
- Verify: emits i64 comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i64 comparisons")
step("Verify: emits i64 comparisons")
var builder = WatBuilder.create()
builder.emit_i64_eq()
builder.emit_i64_ne()
builder.emit_i64_lt_s()
builder.emit_i64_ge_s()
val wat = builder.build()
expect(wat).to_contain("i64.eq")
expect(wat).to_contain("i64.ne")
expect(wat).to_contain("i64.lt_s")
expect(wat).to_contain("i64.ge_s")
```

</details>

#### emits f64 comparisons

- emits f64 comparisons
- Verify: emits f64 comparisons


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits f64 comparisons")
step("Verify: emits f64 comparisons")
var builder = WatBuilder.create()
builder.emit_f64_eq()
builder.emit_f64_lt()
builder.emit_f64_gt()
val wat = builder.build()
expect(wat).to_contain("f64.eq")
expect(wat).to_contain("f64.lt")
expect(wat).to_contain("f64.gt")
```

</details>

#### WatBuilder memory

#### emits i32 load and store

- emits i32 load and store
- Verify: emits i32 load and store


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits i32 load and store")
step("Verify: emits i32 load and store")
var builder = WatBuilder.create()
builder.emit_i32_load(0, 4)
builder.emit_i32_store(8, 4)
val wat = builder.build()
expect(wat).to_contain("i32.load offset=0 align=4")
expect(wat).to_contain("i32.store offset=8 align=4")
```

</details>

#### emits global get and set

- emits global get and set
- Verify: emits global get and set


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits global get and set")
step("Verify: emits global get and set")
var builder = WatBuilder.create()
builder.emit_global_get("heap_ptr")
builder.emit_global_set("heap_ptr")
val wat = builder.build()
expect(wat).to_contain("global.get $heap_ptr")
expect(wat).to_contain("global.set $heap_ptr")
```

</details>

#### WatBuilder logical

#### emits logical ops

- emits logical ops
- Verify: emits logical ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits logical ops")
step("Verify: emits logical ops")
var builder = WatBuilder.create()
builder.emit_i32_and()
builder.emit_i32_or()
builder.emit_i32_xor()
builder.emit_i32_eqz()
val wat = builder.build()
expect(wat).to_contain("i32.and")
expect(wat).to_contain("i32.or")
expect(wat).to_contain("i32.xor")
expect(wat).to_contain("i32.eqz")
```

</details>

#### WasmType

#### converts to text correctly

- converts to text correctly
- Verify: converts to text correctly
   - Expected: WasmType.I32.to_text() equals `i32`
   - Expected: WasmType.I64.to_text() equals `i64`
   - Expected: WasmType.F32.to_text() equals `f32`
   - Expected: WasmType.F64.to_text() equals `f64`
   - Expected: WasmType.FuncRef.to_text() equals `funcref`
   - Expected: WasmType.ExternRef.to_text() equals `externref`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to text correctly")
step("Verify: converts to text correctly")
expect(WasmType.I32.to_text()).to_equal("i32")
expect(WasmType.I64.to_text()).to_equal("i64")
expect(WasmType.F32.to_text()).to_equal("f32")
expect(WasmType.F64.to_text()).to_equal("f64")
expect(WasmType.FuncRef.to_text()).to_equal("funcref")
expect(WasmType.ExternRef.to_text()).to_equal("externref")
```

</details>

#### WasmTarget

#### detects JS glue needs

- detects JS glue needs
- Verify: detects JS glue needs
   - Expected: WasmTarget.Browser.needs_js_glue() is true
   - Expected: WasmTarget.Wasi.needs_js_glue() is false
   - Expected: WasmTarget.Minimal.needs_js_glue() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects JS glue needs")
step("Verify: detects JS glue needs")
expect(WasmTarget.Browser.needs_js_glue()).to_equal(true)
expect(WasmTarget.Wasi.needs_js_glue()).to_equal(false)
expect(WasmTarget.Minimal.needs_js_glue()).to_equal(false)
```

</details>

#### detects WASI import needs

- detects WASI import needs
- Verify: detects WASI import needs
   - Expected: WasmTarget.Wasi.needs_wasi_imports() is true
   - Expected: WasmTarget.Browser.needs_wasi_imports() is false
   - Expected: WasmTarget.Minimal.needs_wasi_imports() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects WASI import needs")
step("Verify: detects WASI import needs")
expect(WasmTarget.Wasi.needs_wasi_imports()).to_equal(true)
expect(WasmTarget.Browser.needs_wasi_imports()).to_equal(false)
expect(WasmTarget.Minimal.needs_wasi_imports()).to_equal(false)
```

</details>

#### WasmTypeMapper

#### maps i64 to i64

- maps i64 to i64
- Verify: maps i64 to i64
   - Expected: mapper.map_type(mir_type) equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps i64 to i64")
step("Verify: maps i64 to i64")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I64)
expect(mapper.map_type(mir_type)).to_equal("i64")
```

</details>

#### maps f64 to f64

- maps f64 to f64
- Verify: maps f64 to f64
   - Expected: mapper.map_type(mir_type) equals `f64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps f64 to f64")
step("Verify: maps f64 to f64")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.F64)
expect(mapper.map_type(mir_type)).to_equal("f64")
```

</details>

#### maps bool to i32

- maps bool to i32
- Verify: maps bool to i32
   - Expected: mapper.map_type(mir_type) equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps bool to i32")
step("Verify: maps bool to i32")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.Bool)
expect(mapper.map_type(mir_type)).to_equal("i32")
```

</details>

#### maps i32 to i32

- maps i32 to i32
- Verify: maps i32 to i32
   - Expected: mapper.map_type(mir_type) equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps i32 to i32")
step("Verify: maps i32 to i32")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I32)
expect(mapper.map_type(mir_type)).to_equal("i32")
```

</details>

#### reports correct size for i64

- reports correct size for i64
- Verify: reports correct size for i64
   - Expected: mapper.size_of(mir_type) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct size for i64")
step("Verify: reports correct size for i64")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I64)
expect(mapper.size_of(mir_type)).to_equal(8)
```

</details>

#### reports correct size for i32

- reports correct size for i32
- Verify: reports correct size for i32
   - Expected: mapper.size_of(mir_type) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct size for i32")
step("Verify: reports correct size for i32")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I32)
expect(mapper.size_of(mir_type)).to_equal(4)
```

</details>

#### reports correct size for bool

- reports correct size for bool
- Verify: reports correct size for bool
   - Expected: mapper.size_of(mir_type) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct size for bool")
step("Verify: reports correct size for bool")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.Bool)
expect(mapper.size_of(mir_type)).to_equal(1)
```

</details>

#### reports correct alignment for f64

- reports correct alignment for f64
- Verify: reports correct alignment for f64
   - Expected: mapper.align_of(mir_type) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports correct alignment for f64")
step("Verify: reports correct alignment for f64")
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.F64)
expect(mapper.align_of(mir_type)).to_equal(8)
```

</details>

#### JsGlueGenerator

#### generates JavaScript glue code

- generates JavaScript glue code
- Verify: generates JavaScript glue code


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates JavaScript glue code")
step("Verify: generates JavaScript glue code")
var glue = JsGlueGenerator.create()
glue.add_binding(BrowserBinding.console_log())
glue.add_export("main")
val js = glue.generate()
expect(js).to_contain("WebAssembly")
expect(js).to_contain("memory")
expect(js).to_contain("loadWasm")
```

</details>

#### WasmBackend creation

#### creates browser backend

- creates browser backend
- Verify: creates browser backend
   - Expected: backend.target.to_text() equals `browser`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates browser backend")
step("Verify: creates browser backend")
val backend = WasmBackend.create(WasmTarget.Browser)
expect(backend.target.to_text()).to_equal("browser")
```

</details>

#### creates wasi backend

- creates wasi backend
- Verify: creates wasi backend
   - Expected: backend.target.to_text() equals `wasi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates wasi backend")
step("Verify: creates wasi backend")
val backend = WasmBackend.create(WasmTarget.Wasi)
expect(backend.target.to_text()).to_equal("wasi")
```

</details>

#### creates minimal backend

- creates minimal backend
- Verify: creates minimal backend
   - Expected: backend.target.to_text() equals `minimal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates minimal backend")
step("Verify: creates minimal backend")
val backend = WasmBackend.create(WasmTarget.Minimal)
expect(backend.target.to_text()).to_equal("minimal")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-WAT-CODEGEN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `52066a78ce956c42dec70835d5ddc56e37321dfb5b31366f78b50fda090f5e9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52066a78ce956c42dec70835d5ddc56e37321dfb5b31366f78b50fda090f5e9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52066a78ce956c42dec70835d5ddc56e37321dfb5b31366f78b50fda090f5e9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/wasm_codegen_spec.spl
mirror: doc/06_spec/unit/compiler/wasm_codegen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/wasm_codegen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/wasm_codegen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/wasm_codegen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/wasm_codegen_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/wasm_codegen_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits i32 const' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/wasm_codegen_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits i64 const' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
