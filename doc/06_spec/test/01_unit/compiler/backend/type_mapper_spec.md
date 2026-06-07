# Type Mapper Specification

> <details>

<!-- sdn-diagram:id=type_mapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_mapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_mapper_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_mapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Mapper Specification

## Scenarios

### Type Mapper

#### maps core primitive types consistently across backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llvm = LlvmTypeMapper.create()
val cranelift = CraneliftTypeMapper.create()
val wasm = WasmTypeMapper.create()
val interp = InterpreterTypeMapper.create()

expect(llvm.map_type(MirType.i64())).to_equal("i64")
expect(cranelift.map_type(MirType.i64())).to_equal("I64")
expect(wasm.map_type(MirType.i64())).to_equal("i64")
expect(interp.map_type(MirType.i64())).to_equal("Int")
expect(llvm.map_type(MirType.bool())).to_equal("i1")
expect(cranelift.map_type(MirType.bool())).to_equal("I8")
expect(wasm.map_type(MirType.bool())).to_equal("i32")
expect(interp.map_type(MirType.bool())).to_equal("Bool")
```

</details>

#### maps pointers according to backend memory model

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr_ty = MirType.ptr(MirType.i64(), false)
val llvm = LlvmTypeMapper.create()
val cranelift = CraneliftTypeMapper.create()
val wasm32 = WasmTypeMapper.create_for_target(CodegenTarget.Wasm32)
val wasm64 = WasmTypeMapper.create_for_target(CodegenTarget.Wasm64)
val interp = InterpreterTypeMapper.create()

expect(llvm.map_type(ptr_ty)).to_equal("ptr")
expect(cranelift.map_type(ptr_ty)).to_equal("R64")
expect(wasm32.map_type(ptr_ty)).to_equal("i32")
expect(wasm64.map_type(ptr_ty)).to_equal("i64")
expect(interp.map_type(ptr_ty)).to_equal("Ptr<Int>")
```

</details>

#### handles composite types using each backend strategy

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tuple_ty = MirType(kind: MirTypeKind.Tuple([MirType.i64(), MirType.bool()]))
val array_ty = MirType(kind: MirTypeKind.Array(MirType.i64(), 4))
val llvm = LlvmTypeMapper.create()
val cranelift = CraneliftTypeMapper.create()
val wasm = WasmTypeMapper.create()
val interp = InterpreterTypeMapper.create()

expect(llvm.map_type(tuple_ty)).to_equal("{ i64, i1 }")
expect(cranelift.map_type(tuple_ty)).to_equal("R64")
expect(wasm.map_type(array_ty)).to_equal("i32")
expect(interp.map_type(array_ty)).to_equal("Array<Int>")
```

</details>

#### keeps target-sensitive size and signature helpers stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llvm = LlvmTypeMapper.create_64bit()
val cranelift = CraneliftTypeMapper.create()
val wasm = WasmTypeMapper.create_wasm32()
val interp = InterpreterTypeMapper.create()
val params = [MirType.i64(), MirType.bool()]

expect(llvm.map_function_signature(params, MirType.i64())).to_equal("i64 (i64, i1)")
expect(cranelift.map_function_signature(params, MirType.i64())).to_equal("(I64, I8) -> I64")
expect(wasm.map_function_signature(params, MirType.unit())).to_equal("(param i64 i32)")
expect(interp.map_function_signature(params, MirType.bool())).to_equal("Function<(Int, Bool) -> Bool>")
expect(llvm.size_of(MirType.ptr(MirType.i64(), false))).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/type_mapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type Mapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
