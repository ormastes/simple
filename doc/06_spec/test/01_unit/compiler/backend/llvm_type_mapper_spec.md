# Llvm Type Mapper Specification

> <details>

<!-- sdn-diagram:id=llvm_type_mapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_type_mapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_type_mapper_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_type_mapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Type Mapper Specification

## Scenarios

### Llvm Type Mapper

#### maps primitive and pointer types

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = LlvmTypeMapper.create()

expect(mapper.map_primitive(PrimitiveType.I64)).to_equal("i64")
expect(mapper.map_primitive(PrimitiveType.F32)).to_equal("float")
expect(mapper.map_primitive(PrimitiveType.Bool)).to_equal("i1")
expect(mapper.map_pointer("i64", Mutability.Mutable)).to_equal("ptr")
```

</details>

#### maps structs arrays tuples and function signatures

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper = LlvmTypeMapper.create()

expect(mapper.map_struct([("x", MirType.i64()), ("y", MirType.f64())])).to_equal("{ i64, double }")
expect(mapper.map_array(MirType.i64(), 3)).to_equal("[3 x i64]")
expect(mapper.map_tuple([MirType.i64(), MirType.bool()])).to_equal("{ i64, i1 }")
expect(mapper.map_function([MirType.i64()], MirType.i64())).to_equal("ptr")
expect(mapper.map_function_signature([MirType.i64(), MirType.i64()], MirType.i64())).to_equal("i64 (i64, i64)")
```

</details>

#### tracks target-specific pointer size and alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapper32 = LlvmTypeMapper.create_32bit()
val mapper64 = LlvmTypeMapper.create_64bit()
val ptr_ty = MirType.ptr(MirType.i64(), false)

expect(mapper32.target_bits).to_equal(32)
expect(mapper64.target_bits).to_equal(64)
expect(mapper32.size_of(ptr_ty)).to_equal(4)
expect(mapper64.size_of(ptr_ty)).to_equal(8)
expect(mapper32.align_of(ptr_ty)).to_equal(4)
expect(mapper64.align_of(ptr_ty)).to_equal(8)
```

</details>

#### keeps named struct registrations in the context

- var ctx = LlvmContext empty
- ctx register struct
   - Expected: ctx.get_struct("Point") equals `Some("%struct.Point")`
   - Expected: ctx.next_struct_name() equals `%struct.anon.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ctx = LlvmContext.empty()
ctx.register_struct("Point", "%struct.Point")

expect(ctx.get_struct("Point")).to_equal(Some("%struct.Point"))
expect(ctx.get_struct("Missing")).to_be_nil()
expect(ctx.next_struct_name()).to_equal("%struct.anon.0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_type_mapper_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Llvm Type Mapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
