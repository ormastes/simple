# LLVM lib backend translation contracts

> Audience: compiler backend engineers owning the DynLib-based LLVM C API path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM lib backend translation contracts

Audience: compiler backend engineers owning the DynLib-based LLVM C API path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/llvm_lib_backend_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: compiler backend engineers owning the DynLib-based LLVM C API path.
Purpose: pin the translation contracts of `llvm_lib_translate_expr.spl`,
`llvm_lib_translate.spl`, and `llvm_lib_backend.spl` — operand translation,
integer equality lowering, nil-return signature mapping, and single-assignment
object emission — so regressions in the translated IR construction surface red.

## Scope and Preconditions

Precondition: the repository working tree contains the compiler backend
sources under `src/compiler/70.backend/backend/`. Direct LLVM C API execution
scenarios are parked (see the pending scenario) because the interpreter cannot
load `std.sffi.llvm`; the remaining scenarios are source-contract regressions
on files that are read at run time, not hardcoded strings.

## Primary Workflow

Read the live backend sources, then assert the operand translation keeps
`translate_operand` calls, integer equality stays on `llvm_build_icmp` before
any `rt_native_eq` fallback, nil signature returns map to the LLVM void type,
and object-code emission stays single-assignment.

## Unsupported / Limitations

The in-process LLVM C API scenarios (context/module/builder lifecycle, target
machine creation, pass pipelines) remain commented out until compiled-mode
execution is available; they are not asserted here.

## Verification and Recovery

A red scenario names the exact file and contract that regressed. To recover,
restore the pinned translation shape in the named backend source; to verify a
fix, rerun `bin/simple test test/01_unit/compiler/backend/llvm_lib_backend_spec.spl`
and require a green `Results:` line.

## Scenarios

### LLVM Lib Backend

#### skipped

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- skipped


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("skipped")
val pending_reason = "interpreter cannot load std.sffi.llvm — module-level var DynLib?/Dict causes semantic error"
expect(pending_reason.len()).to_be_greater_than(0)
```

</details>

#### keeps literal operands on the translated LLVM value path

- keeps literal operands on the translated LLVM value path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps literal operands on the translated LLVM value path")
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl") ?? ""

expect(source).to_contain("val lhs = translate_operand(ctx, mod_, builder, tm, left")
expect(source).to_contain("val rhs = translate_operand(ctx, mod_, builder, tm, right")
expect(source).to_contain("val op_val = translate_operand(ctx, mod_, builder, tm, operand")
expect(source).to_not_contain("val lhs = get_operand_value(left")
expect(source).to_not_contain("val rhs = get_operand_value(right")
expect(source).to_not_contain("val op_val = get_operand_value(operand")
```

</details>

#### keeps integer equality on LLVM icmp before boxed runtime fallback

- keeps integer equality on LLVM icmp before boxed runtime fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps integer equality on LLVM icmp before boxed runtime fallback")
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl") ?? ""

expect(source).to_contain("elif llvm_get_type_kind(left_ty) == 10:")
expect(source).to_contain("llvm_build_icmp(builder, LLVM_INT_EQ, lhs, rhs, \"eq\")")
expect(source).to_contain("llvm_build_icmp(builder, LLVM_INT_NE, lhs, rhs, \"ne\")")
expect(source).to_contain("rt_native_eq")
expect(source).to_contain("rt_native_neq")
```

</details>

#### does not map nil signature returns through native-int fallback

- does not map nil signature returns through native-int fallback
   - Expected: module_source does not contain `val ret_ty = type_mapper.map_type(sig.return_type)`
   - Expected: expr_source does not contain `val ret_ty = tm.map_type(sig.return_type)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not map nil signature returns through native-int fallback")
extern fn rt_file_read_text(path: text) -> text
val module_source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate.spl") ?? ""
val expr_source = rt_file_read_text("src/compiler/70.backend/backend/llvm_lib_translate_expr.spl") ?? ""

expect(module_source).to_contain("if sig.return_type == nil: llvm_void_type_in_context(ctx) else: type_mapper.map_type(sig.return_type)")
expect(expr_source).to_contain("get_local_type(local_types, tm, dest.unwrap().id)")
expect(expr_source).to_contain("if sig.return_type == nil: llvm_void_type_in_context(ctx) else: tm.map_type(sig.return_type)")
expect(module_source.contains("val ret_ty = type_mapper.map_type(sig.return_type)")).to_equal(false)
expect(expr_source.contains("val ret_ty = tm.map_type(sig.return_type)")).to_equal(false)
```

</details>

#### keeps LLVM object code emission single-assignment

- keeps LLVM object code emission single-assignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps LLVM object code emission single-assignment")
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_backend.spl") ?? ""

expect(source).to_not_contain("var object_code: [u8]? = nil")
expect(source).to_not_contain("object_code = Some(llvm_object_code_bytes(obj))")
expect(source).to_contain("object_code: Some(llvm_object_code_bytes(obj))")
expect(source).to_contain("object_code: nil")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4421ce230b3f99decb95a148baef8d163ae05a2d4019803dcb020d23c4f9911e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4421ce230b3f99decb95a148baef8d163ae05a2d4019803dcb020d23c4f9911e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4421ce230b3f99decb95a148baef8d163ae05a2d4019803dcb020d23c4f9911e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/unit/compiler/backend/llvm_lib_backend_spec.spl
mirror: doc/06_spec/unit/compiler/backend/llvm_lib_backend_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/unit/compiler/backend/llvm_lib_backend_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skipped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/llvm_lib_backend_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps literal operands on the translated LLVM value path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/llvm_lib_backend_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps integer equality on LLVM icmp before boxed runtime fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
