# Wasm Codegen Specification

> 1. var builder = WatBuilder create

<!-- sdn-diagram:id=wasm_codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_codegen_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Codegen Specification

## Scenarios

### WAT Codegen

#### WatBuilder basics

#### creates empty module

1. var builder = WatBuilder create
2. builder begin module
3. builder end module


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.begin_module("test")
builder.end_module()
val wat = builder.build()
expect(wat).to_contain("(module $test")
expect(wat).to_contain(")")
```

</details>

#### emits i32 const

1. var builder = WatBuilder create
2. builder emit i32 const


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_i32_const(42)
val wat = builder.build()
expect(wat).to_contain("i32.const 42")
```

</details>

#### emits i64 const

1. var builder = WatBuilder create
2. builder emit i64 const


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_i64_const(100)
val wat = builder.build()
expect(wat).to_contain("i64.const 100")
```

</details>

#### emits f64 const

1. var builder = WatBuilder create
2. builder emit f64 const


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_f64_const(3.14)
val wat = builder.build()
expect(wat).to_contain("f64.const")
```

</details>

#### emits local get and set by name

1. var builder = WatBuilder create
2. builder emit local named get
3. builder emit local named set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_local_named_get("x")
builder.emit_local_named_set("y")
val wat = builder.build()
expect(wat).to_contain("local.get $x")
expect(wat).to_contain("local.set $y")
```

</details>

#### emits call by name

1. var builder = WatBuilder create
2. builder emit call named


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_call_named("my_func")
val wat = builder.build()
expect(wat).to_contain("call $my_func")
```

</details>

#### WatBuilder control flow

#### emits block and end

1. var builder = WatBuilder create
2. builder emit block
3. builder emit end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = WatBuilder create
2. builder emit loop
3. builder emit end


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_loop("loop_start")
builder.emit_end()
val wat = builder.build()
expect(wat).to_contain("(loop $loop_start")
```

</details>


</details>

#### emits branch instructions

1. var builder = WatBuilder create
2. builder emit br
3. builder emit br if


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_br("target")
builder.emit_br_if("cond_target")
val wat = builder.build()
expect(wat).to_contain("br $target")
expect(wat).to_contain("br_if $cond_target")
```

</details>

#### emits return

1. var builder = WatBuilder create
2. builder emit return


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_return()
val wat = builder.build()
expect(wat).to_contain("return")
```

</details>

#### emits unreachable

1. var builder = WatBuilder create
2. builder emit unreachable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_unreachable()
val wat = builder.build()
expect(wat).to_contain("unreachable")
```

</details>

#### WatBuilder arithmetic

#### emits i64 arithmetic

1. var builder = WatBuilder create
2. builder emit i64 add
3. builder emit i64 sub
4. builder emit i64 mul
5. builder emit i64 div s
6. builder emit i64 rem s


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = WatBuilder create
2. builder emit f64 add
3. builder emit f64 sub
4. builder emit f64 mul
5. builder emit f64 div


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = WatBuilder create
2. builder emit i64 eq
3. builder emit i64 ne
4. builder emit i64 lt s
5. builder emit i64 ge s


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = WatBuilder create
2. builder emit f64 eq
3. builder emit f64 lt
4. builder emit f64 gt


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = WatBuilder create
2. builder emit i32 load
3. builder emit i32 store


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = WatBuilder.create()
builder.emit_i32_load(0, 4)
builder.emit_i32_store(8, 4)
val wat = builder.build()
expect(wat).to_contain("i32.load offset=0 align=4")
expect(wat).to_contain("i32.store offset=8 align=4")
```

</details>

#### emits global get and set

1. var builder = WatBuilder create
2. builder emit global get
3. builder emit global set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var builder = WatBuilder create
2. builder emit i32 and
3. builder emit i32 or
4. builder emit i32 xor
5. builder emit i32 eqz


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WasmTarget.Browser.needs_js_glue()).to_equal(true)
expect(WasmTarget.Wasi.needs_js_glue()).to_equal(false)
expect(WasmTarget.Minimal.needs_js_glue()).to_equal(false)
```

</details>

#### detects WASI import needs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WasmTarget.Wasi.needs_wasi_imports()).to_equal(true)
expect(WasmTarget.Browser.needs_wasi_imports()).to_equal(false)
expect(WasmTarget.Minimal.needs_wasi_imports()).to_equal(false)
```

</details>

#### WasmTypeMapper

#### maps i64 to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I64)
expect(mapper.map_type(mir_type)).to_equal("i64")
```

</details>

#### maps f64 to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.F64)
expect(mapper.map_type(mir_type)).to_equal("f64")
```

</details>

#### maps bool to i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.Bool)
expect(mapper.map_type(mir_type)).to_equal("i32")
```

</details>

#### maps i32 to i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I32)
expect(mapper.map_type(mir_type)).to_equal("i32")
```

</details>

#### reports correct size for i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I64)
expect(mapper.size_of(mir_type)).to_equal(8)
```

</details>

#### reports correct size for i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.I32)
expect(mapper.size_of(mir_type)).to_equal(4)
```

</details>

#### reports correct size for bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.Bool)
expect(mapper.size_of(mir_type)).to_equal(1)
```

</details>

#### reports correct alignment for f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper__create_wasm32()
val mir_type = MirType(kind: MirTypeKind.F64)
expect(mapper.align_of(mir_type)).to_equal(8)
```

</details>

#### JsGlueGenerator

#### generates JavaScript glue code

1. var glue = JsGlueGenerator create
2. glue add binding
3. glue add export


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend.create(WasmTarget.Browser)
expect(backend.target.to_text()).to_equal("browser")
```

</details>

#### creates wasi backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend.create(WasmTarget.Wasi)
expect(backend.target.to_text()).to_equal("wasi")
```

</details>

#### creates minimal backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = WasmBackend.create(WasmTarget.Minimal)
expect(backend.target.to_text()).to_equal("minimal")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/wasm_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WAT Codegen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
