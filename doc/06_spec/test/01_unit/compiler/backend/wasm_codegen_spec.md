# Wasm Codegen Specification

> 1. builder begin module

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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Codegen Specification

## Scenarios

### Wasm Codegen

#### emits direct WatBuilder strings

1. builder begin module
2. builder emit i32 const
3. builder emit i64 const
4. builder emit f64 const
5. builder emit local named get
6. builder emit local named set
7. builder emit call named
8. builder end module


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wat = wat_for(\builder:
    builder.begin_module("test")
    builder.emit_i32_const(42)
    builder.emit_i64_const(100)
    builder.emit_f64_const(3.14)
    builder.emit_local_named_get("x")
    builder.emit_local_named_set("y")
    builder.emit_call_named("my_func")
    builder.end_module()
)

expect(wat).to_contain("(module $test")
expect(wat).to_contain("i32.const 42")
expect(wat).to_contain("i64.const 100")
expect(wat).to_contain("f64.const 3.14")
expect(wat).to_contain("local.get $x")
expect(wat).to_contain("local.set $y")
expect(wat).to_contain("call $my_func")
```

</details>

#### emits control flow and arithmetic instructions

1. builder emit block
2. builder emit loop
3. builder emit br
4. builder emit br if
5. builder emit return
6. builder emit unreachable
7. builder emit end
8. builder emit end


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wat = wat_for(\builder:
    builder.emit_block("exit")
    builder.emit_loop("loop_start")
    builder.emit_br("target")
    builder.emit_br_if("cond_target")
    builder.emit_return()
    builder.emit_unreachable()
    builder.emit_end()
    builder.emit_end()
)

expect(wat).to_contain("(block $exit")
expect(wat).to_contain("(loop $loop_start")
expect(wat).to_contain("br $target")
expect(wat).to_contain("br_if $cond_target")
expect(wat).to_contain("return")
expect(wat).to_contain("unreachable")
```

</details>

#### renders wasm value types and target helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WasmType.I32.to_text()).to_equal("i32")
expect(WasmType.I64.to_text()).to_equal("i64")
expect(WasmType.F32.to_text()).to_equal("f32")
expect(WasmType.F64.to_text()).to_equal("f64")
expect(WasmType.FuncRef.to_text()).to_equal("funcref")
expect(WasmType.ExternRef.to_text()).to_equal("externref")

expect(WasmTarget.Browser.needs_js_glue()).to_equal(true)
expect(WasmTarget.Wasi.needs_js_glue()).to_equal(false)
expect(WasmTarget.Minimal.needs_js_glue()).to_equal(false)
expect(WasmTarget.Wasi.needs_wasi_imports()).to_equal(true)
expect(WasmTarget.Browser.needs_wasi_imports()).to_equal(false)
expect(WasmTarget.Minimal.needs_wasi_imports()).to_equal(false)
```

</details>

#### maps primitive MIR types for wasm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper.create_wasm32()

expect(mapper.map_type(MirType(kind: MirTypeKind.I64))).to_equal("i64")
expect(mapper.map_type(MirType(kind: MirTypeKind.F64))).to_equal("f64")
expect(mapper.map_type(MirType(kind: MirTypeKind.Bool))).to_equal("i32")
expect(mapper.map_type(MirType(kind: MirTypeKind.I32))).to_equal("i32")
expect(mapper.map_type(MirType(kind: MirTypeKind.Unit))).to_equal("i32")
```

</details>

#### reports primitive sizes and alignments for wasm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = WasmTypeMapper.create_wasm32()

expect(mapper.size_of(MirType(kind: MirTypeKind.I64))).to_equal(8)
expect(mapper.size_of(MirType(kind: MirTypeKind.I32))).to_equal(4)
expect(mapper.size_of(MirType(kind: MirTypeKind.Bool))).to_equal(1)
expect(mapper.align_of(MirType(kind: MirTypeKind.F64))).to_equal(8)
expect(mapper.align_of(MirType(kind: MirTypeKind.I16))).to_equal(2)
expect(mapper.align_of(MirType(kind: MirTypeKind.Bool))).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/wasm_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wasm Codegen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
