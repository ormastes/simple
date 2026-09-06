# Hir Block Tail Invariants Source Specification

> Tests covering HIR block tail invariants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Block Tail Invariants Source Specification

## Scenarios

### HIR block tail invariants

#### guards tail expression payload matching by exact discriminator

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards tail expression payload matching by exact discriminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards tail expression payload matching by exact discriminator")
val expressions = source("src/compiler/20.hir/hir_lowering/expressions.spl")

expect(expressions).to_contain("val expr_stmt_disc = rt_enum_discriminant(HirStmtKind.Expr(block_value_expr))")
expect(expressions).to_contain("val return_expr_disc = rt_enum_discriminant(HirExprKind.Return(nil))")
expect(expressions).to_contain("if rt_enum_discriminant(lowered.kind) == expr_stmt_disc:")
expect(expressions).to_contain("case HirStmtKind.Expr(expr):")
expect(expressions).to_contain("if rt_enum_discriminant(expr.kind) == return_expr_disc:")
```

</details>

#### lowers the mandatory HIR function return type directly

- lowers the mandatory HIR function return type directly
   - Expected: functions does not contain `if fn_.return_type.?:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers the mandatory HIR function return type directly")
val functions = source("src/compiler/50.mir/_MirLowering/function_lowering.spl")

expect(functions).to_contain("val return_type = self.lower_type(fn_.return_type)")
expect(functions.contains("if fn_.return_type.?:")).to_equal(false)
```

</details>

#### keeps explicit bootstrap returns as statements, not tail values

- keeps explicit bootstrap returns as statements, not tail values


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps explicit bootstrap returns as statements, not tail values")
val items = source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")

expect(items).to_contain("val expr_stmt_disc = rt_enum_discriminant(HirStmtKind.Expr(value_expr))")
expect(items).to_contain("val return_expr_disc = rt_enum_discriminant(HirExprKind.Return(nil))")
expect(items).to_contain("if rt_enum_discriminant(stmt.kind) == expr_stmt_disc:")
expect(items).to_contain("case HirStmtKind.Expr(expr):")
expect(items).to_contain("if rt_enum_discriminant(expr.kind) == return_expr_disc:")
expect(items).to_contain("stmts.push(stmt)")
```

</details>

#### preserves encoded Dict return types in bootstrap HIR

- preserves encoded Dict return types in bootstrap HIR


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves encoded Dict return types in bootstrap HIR")
val items = source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")

expect(items).to_contain("if tag == TYPE_DICT:")
expect(items).to_contain("if is_dict_tag(tag):")
expect(items).to_contain("self.bootstrap_hir_type_from_tag(dict_type_get_key(dict_id))")
expect(items).to_contain("self.bootstrap_hir_type_from_tag(dict_type_get_value(dict_id))")
```

</details>

#### guards MIR Dict type payload extraction by exact discriminator

- guards MIR Dict type payload extraction by exact discriminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards MIR Dict type payload extraction by exact discriminator")
val functions = source("src/compiler/50.mir/_MirLowering/function_lowering.spl")

expect(functions).to_contain("val dict_type_disc = rt_enum_discriminant(HirTypeKind.Dict(type_, type_))")
expect(functions).to_contain("if rt_enum_discriminant(type_.kind) == dict_type_disc:")
expect(functions).to_contain("case HirTypeKind.Dict(key, value):")
```

</details>

#### predispatches explicit Return before the raw expression match

- predispatches explicit Return before the raw expression match


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("predispatches explicit Return before the raw expression match")
val expressions = source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(expressions).to_contain("val return_disc = rt_enum_discriminant(HirExprKind.Return(nil))")
expect(expressions).to_contain("if expr_disc == return_disc:")
expect(expressions).to_contain("case HirExprKind.Return(value):")
expect(expressions).to_contain("return self.lower_return_expr(value)")
expect(expressions).to_contain("case Return(value):\n                self.lower_return_expr(value)")
```

</details>

#### extracts validated HIR Expr statements without pattern binding

- extracts validated HIR Expr statements without pattern binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts validated HIR Expr statements without pattern binding")
val statements = source("src/compiler/50.mir/mir_lowering_stmts.spl")

expect(statements).to_contain("extern fn rt_enum_payload(value: HirStmtKind) -> HirExpr")
expect(statements).to_contain("val expr: HirExpr = rt_enum_payload(stmt_kind_value)")
expect(statements).to_contain("empty HIR expression-statement payload")
```

</details>

#### predispatches Index through one complete lowering helper

- predispatches Index through one complete lowering helper
   - Expected: expressions does not contain `if dict_mir_type != nil:`
   - Expected: expressions does not contain `if base_mir_type != nil:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("predispatches Index through one complete lowering helper")
val expressions = source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(expressions).to_contain("extern fn rt_enum_payload(value: Any) -> i64")
expect(expressions).to_contain("extern fn rt_tuple_get(tuple: i64, index: i64) -> i64")
expect(expressions).to_contain("me lower_index_expr_from_hir(expr_value: HirExpr) -> LocalId:")
expect(expressions).to_contain("val payload = rt_enum_payload(expr_value.kind)")
expect(expressions).to_contain("val base: HirExpr = rt_tuple_get(payload, 0)")
expect(expressions).to_contain("val index: HirExpr = rt_tuple_get(payload, 1)")
expect(expressions).to_contain("if base == nil or index == nil:")
expect(expressions).to_contain("empty HIR Index payload")
expect(expressions).to_contain("val has_result_hir_type = expr_value.has_type_ == true and expr_value.type_ != nil")
expect(expressions).to_contain("self.lower_index_expr(base, index, has_result_hir_type, expr_value.type_)")
expect(expressions).to_contain("me lower_index_expr(base: HirExpr, index: HirExpr, has_index_result_hir_type: bool, index_result_hir_type: HirType) -> LocalId:")
expect(expressions).to_contain("for item in self.builder.locals:")
expect(expressions).to_contain("if item.id.id == base_local.id:")
expect(expressions).to_contain("resolved_dict_mir_type = item.type_")
expect(expressions).to_contain("if not has_dict_mir_type and base.has_type_ == true and base.type_ != nil:")
expect(expressions).to_contain("if has_base_mir_type:")
expect(expressions.contains("if dict_mir_type != nil:")).to_equal(false)
expect(expressions.contains("if base_mir_type != nil:")).to_equal(false)
expect(expressions).to_contain("elif not result_type_from_base and has_index_result_hir_type:")
expect(expressions).to_contain("val index_disc = rt_enum_discriminant(HirExprKind.Index(nil_expr, nil_expr))")
expect(expressions).to_contain("return self.lower_index_expr_from_hir(expr_value)")
expect(expressions).to_contain("case Index(base, index):\n                val has_index_result_type = expr_value.has_type_ == true and expr_value.type_ != nil")
expect(expressions).to_contain("self.lower_index_expr(base, index, has_index_result_type, expr_value.type_)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR block tail invariants.
- HIR block tail invariants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `9c45ba627df22779742c5170b9c2ec3f6ac410383311c2d57c322c367cc6af75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c45ba627df22779742c5170b9c2ec3f6ac410383311c2d57c322c367cc6af75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c45ba627df22779742c5170b9c2ec3f6ac410383311c2d57c322c367cc6af75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards tail expression payload matching by exact discriminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers the mandatory HIR function return type directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_block_tail_invariants_source_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps explicit bootstrap returns as statements, not tail values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
