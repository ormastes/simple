# Type Mapper Specification

> Tests covering Type Mapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Mapper Specification

## Scenarios

### Type Mapper

#### maps core primitive types consistently across backends

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps core primitive types consistently across backends
   - Expected: llvm.map_type(MirType.i64()) equals `i64`
   - Expected: cranelift.map_type(MirType.i64()) equals `I64`
   - Expected: wasm.map_type(MirType.i64()) equals `i64`
   - Expected: interp.map_type(MirType.i64()) equals `Int`
   - Expected: llvm.map_type(MirType.bool()) equals `i1`
   - Expected: cranelift.map_type(MirType.bool()) equals `I8`
   - Expected: wasm.map_type(MirType.bool()) equals `i32`
   - Expected: interp.map_type(MirType.bool()) equals `Bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps core primitive types consistently across backends")
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

- maps pointers according to backend memory model
   - Expected: llvm.map_type(ptr_ty) equals `ptr`
   - Expected: cranelift.map_type(ptr_ty) equals `R64`
   - Expected: wasm32.map_type(ptr_ty) equals `i32`
   - Expected: wasm64.map_type(ptr_ty) equals `i64`
   - Expected: interp.map_type(ptr_ty) equals `Ptr<Int>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps pointers according to backend memory model")
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

- handles composite types using each backend strategy
   - Expected: llvm.map_type(tuple_ty) equals `{ i64, i1 }`
   - Expected: cranelift.map_type(tuple_ty) equals `R64`
   - Expected: wasm.map_type(array_ty) equals `i32`
   - Expected: c.map_type(tuple_ty) equals `std::tuple<int64_t, int64_t>`
   - Expected: interp.map_type(array_ty) equals `Array<Int>`
   - Expected: interp.map_type(tuple_ty) equals `Tuple<Int, Bool>`
   - Expected: interp.map_union([MirType.i64(), MirType.bool()]) equals `Union<Int, Bool>`
   - Expected: interp.map_struct([("count", MirType.i64()), ("ready", MirType.bool())]) equals `Struct<count: Int, ready: Bool>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles composite types using each backend strategy")
val tuple_ty = MirType(kind: MirTypeKind.Tuple([MirType.i64(), MirType.bool()]))
val array_ty = MirType(kind: MirTypeKind.Array(MirType.i64(), 4))
val llvm = LlvmTypeMapper.create()
val cranelift = CraneliftTypeMapper.create()
val wasm = WasmTypeMapper.create()
val interp = InterpreterTypeMapper.create()
val c = CTypeMapper.create()

expect(llvm.map_type(tuple_ty)).to_equal("{ i64, i1 }")
expect(cranelift.map_type(tuple_ty)).to_equal("R64")
expect(wasm.map_type(array_ty)).to_equal("i32")
expect(c.map_type(tuple_ty)).to_equal("std::tuple<int64_t, int64_t>")
expect(interp.map_type(array_ty)).to_equal("Array<Int>")
expect(interp.map_type(tuple_ty)).to_equal("Tuple<Int, Bool>")
expect(interp.map_union([MirType.i64(), MirType.bool()])).to_equal("Union<Int, Bool>")
expect(interp.map_struct([("count", MirType.i64()), ("ready", MirType.bool())])).to_equal("Struct<count: Int, ready: Bool>")
```

</details>

#### keeps target-sensitive size and signature helpers stable

- keeps target-sensitive size and signature helpers stable
   - Expected: llvm.map_function_signature(params, MirType.i64()) equals `i64 (i64, i1)`
   - Expected: cranelift.map_function_signature(params, MirType.i64()) equals `(I64, I8) -> I64`
   - Expected: wasm.map_function_signature(params, MirType.unit()) equals `(param i64 i32)`
   - Expected: wasm.map_function_signature(params, MirType.i64()) equals `(param i64 i32) (result i64)`
   - Expected: interp.map_function_signature(params, MirType.bool()) equals `Function<(Int, Bool) -> Bool>`
   - Expected: llvm.size_of(MirType.ptr(MirType.i64(), false)) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps target-sensitive size and signature helpers stable")
val llvm = LlvmTypeMapper.create_64bit()
val cranelift = CraneliftTypeMapper.create()
val wasm = WasmTypeMapper.create_wasm32()
val interp = InterpreterTypeMapper.create()
val params = [MirType.i64(), MirType.bool()]

expect(llvm.map_function_signature(params, MirType.i64())).to_equal("i64 (i64, i1)")
expect(cranelift.map_function_signature(params, MirType.i64())).to_equal("(I64, I8) -> I64")
expect(wasm.map_function_signature(params, MirType.unit())).to_equal("(param i64 i32)")
expect(wasm.map_function_signature(params, MirType.i64())).to_equal("(param i64 i32) (result i64)")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Type Mapper.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3aadf7f02c71aad0a60d82e2e5a7912b427b3caf53f1c9e97299a0ab0482a719`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3aadf7f02c71aad0a60d82e2e5a7912b427b3caf53f1c9e97299a0ab0482a719`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3aadf7f02c71aad0a60d82e2e5a7912b427b3caf53f1c9e97299a0ab0482a719`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/backend/type_mapper_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/type_mapper_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/type_mapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/type_mapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/type_mapper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/type_mapper_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps core primitive types consistently across backends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/type_mapper_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps pointers according to backend memory model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/type_mapper_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles composite types using each backend strategy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
