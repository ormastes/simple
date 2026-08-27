# Llvm Lib Backend Specification

> Tests covering LLVM Lib Backend.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Lib Backend Specification

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
   - Expected: source does not contain `var object_code: [u8]? = nil`
   - Expected: source does not contain `object_code = Some(llvm_object_code_bytes(obj))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps LLVM object code emission single-assignment")
extern fn rt_file_read_text(path: text) -> text
val source = rt_file_read_text("src/compiler/70.backend/backend/llvm_backend.spl") ?? ""

expect(source.contains("var object_code: [u8]? = nil")).to_equal(false)
expect(source.contains("object_code = Some(llvm_object_code_bytes(obj))")).to_equal(false)
expect(source).to_contain("object_code: Some(llvm_object_code_bytes(obj))")
expect(source).to_contain("object_code: nil")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_lib_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM Lib Backend.
- LLVM Lib Backend

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e394483722585a6a6e67f9e341e94f67313263f4c10d9ea5783b852e948012c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e394483722585a6a6e67f9e341e94f67313263f4c10d9ea5783b852e948012c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e394483722585a6a6e67f9e341e94f67313263f4c10d9ea5783b852e948012c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/backend/llvm_lib_backend_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/llvm_lib_backend_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/backend/llvm_lib_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/llvm_lib_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/llvm_lib_backend_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/backend/llvm_lib_backend_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/backend/llvm_lib_backend_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skipped' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_lib_backend_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps literal operands on the translated LLVM value path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/llvm_lib_backend_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps integer equality on LLVM icmp before boxed runtime fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
