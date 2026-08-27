# Llvm Pointer Return Null Specification

> Tests covering LLVM pointer return null.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Pointer Return Null Specification

## Scenarios

### LLVM pointer return null

#### emits null instead of integer zero for pointer returns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits null instead of integer zero for pointer returns
   - Expected: output does not contain `ret ptr 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits null instead of integer zero for pointer returns")
val output = llvm_pointer_return_output()

expect(output).to_contain("ret ptr null")
expect(output.contains("ret ptr 0")).to_equal(false)
```

</details>

#### mirrors string globals into text for bootstrap flush

- mirrors string globals into text for bootstrap flush


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mirrors string globals into text for bootstrap flush")
val translator = MirToLlvm.create("test.llvm.pointer_return", CodegenTarget.X86_64, nil)
translator.translate_const(
    LocalId(id: 1),
    MirConstValue.Str("hello"),
    MirType.ptr(MirType.i64(), false)
)

expect(translator.string_global_text).to_contain("@.str.0 = private unnamed_addr constant")
expect(translator.string_global_text).to_contain("hello\\00")
```

</details>

#### keeps libLLVM pointer zero constants on the null path

- keeps libLLVM pointer zero constants on the null path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps libLLVM pointer zero constants on the null path")
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl") ?? ""

expect(source).to_contain("if v == 0 and llvm_get_type_kind(llvm_ty) == 14:")
expect(source).to_contain("llvm_const_null(llvm_ty)")
```

</details>

#### renders string function pointer calls as LLVM symbol callees

- renders string function pointer calls as LLVM symbol callees
   - Expected: output does not contain `call i64 0()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders string function pointer calls as LLVM symbol callees")
val translator = MirToLlvm.create("test.llvm.direct_call", CodegenTarget.X86_64, nil)
val func = MirOperand(kind: MirOperandKind.Const(
    MirConstValue.Str("callee_symbol"),
    MirType(kind: MirTypeKind.FuncPtr(MirSignature(params: [], return_type: MirType.i64(), is_variadic: false)))
))
translator.translate_call(Some(LocalId(id: 1)), func, [])
val output = translator.builder.build()

expect(output).to_contain("%l1 = call i64 @callee_symbol()")
expect(output.contains("call i64 0()")).to_equal(false)
```

</details>

#### routes dict literal insertion through the exported runtime setter

- routes dict literal insertion through the exported runtime setter
   - Expected: output does not contain `@rt_dict_insert`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes dict literal insertion through the exported runtime setter")
val translator = MirToLlvm.create("test.llvm.dict_insert", CodegenTarget.X86_64, nil)
val func = MirOperand(kind: MirOperandKind.Const(
    MirConstValue.Str("rt_dict_insert"),
    MirType(kind: MirTypeKind.FuncPtr(MirSignature(
        params: [MirType.i64(), MirType.i64(), MirType.i64()],
        return_type: MirType.i64(),
        is_variadic: false
    )))
))
translator.translate_call(Some(LocalId(id: 1)), func, [
    MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), MirType.i64())),
    MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(2), MirType.i64())),
    MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(3), MirType.i64()))
])
val output = translator.builder.build()

expect(output).to_contain("@rt_dict_set")
expect(output.contains("@rt_dict_insert")).to_equal(false)
```

</details>

#### does not emit nil as a getelementptr element type

- does not emit nil as a getelementptr element type
   - Expected: output does not contain `getelementptr nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not emit nil as a getelementptr element type")
val translator = MirToLlvm.create("test.llvm.gep", CodegenTarget.X86_64, nil)
translator.translate_gep(
    LocalId(id: 1),
    MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
    [MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), MirType.i64()))]
)
val output = translator.builder.build()

expect(output).to_contain("%l1 = getelementptr i64")
expect(output.contains("getelementptr nil")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM pointer return null.
- LLVM pointer return null

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c522876ee64859c40d29e4ee6a26122638eef3e894291726e8cda9bfaa9d847`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c522876ee64859c40d29e4ee6a26122638eef3e894291726e8cda9bfaa9d847`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c522876ee64859c40d29e4ee6a26122638eef3e894291726e8cda9bfaa9d847`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_pointer_return_null_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/llvm_pointer_return_null_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_pointer_return_null_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits null instead of integer zero for pointer returns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mirrors string globals into text for bootstrap flush' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps libLLVM pointer zero constants on the null path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
