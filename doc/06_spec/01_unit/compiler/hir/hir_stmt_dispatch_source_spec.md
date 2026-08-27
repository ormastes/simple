# Hir Stmt Dispatch Source Specification

> Tests covering HIR statement dispatch source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Stmt Dispatch Source Specification

## Scenarios

### HIR statement dispatch source

#### uses runtime discriminants before struct-shadowed Expr dispatch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses runtime discriminants before struct-shadowed Expr dispatch
   - Expected: source does not contain `fn hir_stmt_kind_disc(k: StmtKind) -> i64:\n    match k:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses runtime discriminants before struct-shadowed Expr dispatch")
val source = read_source("src/compiler/20.hir/hir_lowering/statements.spl")
expect(source).to_contain("fn hir_stmt_kind_disc(k: StmtKind) -> i64:\n    rt_enum_discriminant(k)")
expect(source.contains("fn hir_stmt_kind_disc(k: StmtKind) -> i64:\n    match k:")).to_equal(false)
```

</details>

#### compares runtime tags for bootstrap statement predispatch

- compares runtime tags for bootstrap statement predispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("compares runtime tags for bootstrap statement predispatch")
val source = read_source("src/compiler/20.hir/hir_lowering/statements.spl")

expect(source).to_contain("hir_stmt_kind_disc(StmtKind.Val(\"\", nil, sk_dummy))")
expect(source).to_contain("hir_stmt_kind_disc(StmtKind.Var(\"\", nil, nil))")
expect(source).to_contain("hir_stmt_kind_disc(StmtKind.Return(nil))")
expect(source).to_contain("hir_stmt_kind_disc(StmtKind.Assign(sk_dummy, nil, sk_dummy))")
expect(source).to_contain("hir_stmt_kind_disc(StmtKind.Expr(sk_dummy))")
```

</details>

#### unwraps initialized Var before local shape registration

- unwraps initialized Var before local shape registration
   - Expected: source does not contain `if val vr_init_present = vr_init:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwraps initialized Var before local shape registration")
val source = read_source("src/compiler/20.hir/hir_lowering/statements.spl")

expect(source).to_contain("if vr_init.?:\n                val vr_init_present = vr_init ?? sk_dummy")
expect(source.contains("if val vr_init_present = vr_init:")).to_equal(false)
```

</details>

#### unwraps HIR symbol lookups without pattern binding

- unwraps HIR symbol lookups without pattern binding
   - Expected: types_source does not contain `if val sym = found:`
   - Expected: module_source does not contain `if val found_symbol = found:`
   - Expected: declaration_source does not contain `if val found_symbol = fn_symbol_lookup:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwraps HIR symbol lookups without pattern binding")
val types_source = read_source("src/compiler/20.hir/hir_types.spl")
val module_source = read_source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val declaration_source = read_source("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")

expect(types_source.contains("if val sym = found:")).to_equal(false)
expect(module_source.contains("if val found_symbol = found:")).to_equal(false)
expect(declaration_source.contains("if val found_symbol = fn_symbol_lookup:")).to_equal(false)
expect(declaration_source).to_contain("if fn_symbol_lookup.?:\n                fn_symbol_id = fn_symbol_lookup.unwrap()")
```

</details>

#### unwraps optional SymbolIds without compact pattern binding

- unwraps optional SymbolIds without compact pattern binding
   - Expected: expr_source does not contain `if val fld_tb_sym3 = fld_tuple_base_sym:`
   - Expected: expr_source does not contain `if val fld_base_sym = fld_base_sym_opt:`
   - Expected: stmt_source does not contain `if val td_bs = td_base_sym:`
   - Expected: async_source does not contain `if val future_symbol = future_symbol_opt:`
   - Expected: mir_fn_source does not contain `if val found_symbol = param.symbol:`
   - Expected: inline_policy_source does not contain `match type_.kind:`
   - Expected: inline_driver_source does not contain `match type_.kind:`
   - Expected: symbol_source does not contain `if val found = sym:`
   - Expected: symbol_source does not contain `if val found_type_symbol = type_sym:`
   - Expected: mir_expr_source does not contain `if expr_disc == namedvar_pre_disc:\n            match expr_value.kind:`
   - Expected: mir_expr_source does not contain `if val binop_left_ty = self.local_mir_type_of(left_local):`
   - Expected: mir_expr_source does not contain `if val binop_right_ty = self.local_mir_type_of(right_local):`
   - Expected: mir_expr_source does not contain `if val left_arr_ty = self.local_mir_type_of(left_local):`
   - Expected: mir_expr_source does not contain `if val right_arr_ty = self.local_mir_type_of(right_local):`
   - Expected: mir_expr_source does not contain `if val left_type = self.local_mir_type_of(left_local):`
   - Expected: mir_expr_source does not contain `if val right_type = self.local_mir_type_of(right_local):`
   - Expected: mir_expr_source does not contain `if val found_base_type = base_type:`
   - Expected: mir_stmt_source does not contain `case Field(base, field, resolved):`


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unwraps optional SymbolIds without compact pattern binding")
val expr_source = read_source("src/compiler/20.hir/hir_lowering/expressions.spl")
val stmt_source = read_source("src/compiler/20.hir/hir_lowering/statements.spl")
val async_source = read_source("src/compiler/20.hir/hir_lowering/async.spl")
val mir_fn_source = read_source("src/compiler/50.mir/_MirLowering/function_lowering.spl")
val mir_expr_source = read_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")
val mir_stmt_source = read_source("src/compiler/50.mir/mir_lowering_stmts.spl")
val inline_policy_source = read_source("src/compiler/60.mir_opt/mir_opt/_Inline/policy.spl")
val inline_driver_source = read_source("src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl")
val symbol_source = read_source("src/compiler/20.hir/hir_types.spl")

expect(expr_source.contains("if val fld_tb_sym3 = fld_tuple_base_sym:")).to_equal(false)
expect(expr_source.contains("if val fld_base_sym = fld_base_sym_opt:")).to_equal(false)
expect(stmt_source.contains("if val td_bs = td_base_sym:")).to_equal(false)
expect(async_source.contains("if val future_symbol = future_symbol_opt:")).to_equal(false)
expect(stmt_source).to_contain("val expr_assign_disc = hir_expr_kind_disc(ExprKind.Assign(sk_dummy, nil, sk_dummy))")
expect(stmt_source).to_contain("val assign_payload: [Any] = rt_enum_payload(expr_kind)")
expect(stmt_source).to_contain("val target_t: Expr = assign_payload[0]")
expect(stmt_source).to_contain("val value_t: Expr = assign_payload[2]")
expect(mir_fn_source.contains("if val found_symbol = param.symbol:")).to_equal(false)
expect(mir_fn_source).to_contain("val found_symbol: SymbolId = param.symbol\n            self.local_map[found_symbol.id] = pli + parameter_local_offset")
expect(mir_expr_source).to_contain("extern fn rt_enum_payload(value: Any) -> Any")
expect(mir_expr_source).to_contain("extern fn rt_value_as_int(value: i64) -> i64")
expect(mir_expr_source).to_contain("val namedvar_payload: [Any] = rt_enum_payload(expr_value.kind)")
expect(mir_expr_source).to_contain("val symbol_t: SymbolId = namedvar_payload[0]")
expect(mir_expr_source).to_contain("val name_t: text = namedvar_payload[1]")
expect(mir_expr_source).to_contain("val pre_sym_id = rt_value_as_int(symbol_t.id)")
expect(inline_policy_source).to_contain("case Const(value, _):\n                match value:")
expect(inline_policy_source.contains("match type_.kind:")).to_equal(false)
expect(inline_driver_source.contains("match type_.kind:")).to_equal(false)
expect(inline_driver_source).to_contain("case Int(id): Some(id)")
expect(symbol_source.contains("if val found = sym:")).to_equal(false)
expect(symbol_source.contains("if val found_type_symbol = type_sym:")).to_equal(false)
expect(symbol_source).to_contain("val found: HirSymbol? = self.symbols[raw]")
expect(mir_expr_source.contains("if expr_disc == namedvar_pre_disc:\n            match expr_value.kind:")).to_equal(false)
expect(mir_expr_source.contains("if val binop_left_ty = self.local_mir_type_of(left_local):")).to_equal(false)
expect(mir_expr_source.contains("if val binop_right_ty = self.local_mir_type_of(right_local):")).to_equal(false)
expect(mir_expr_source.contains("if val left_arr_ty = self.local_mir_type_of(left_local):")).to_equal(false)
expect(mir_expr_source.contains("if val right_arr_ty = self.local_mir_type_of(right_local):")).to_equal(false)
expect(mir_expr_source.contains("if val left_type = self.local_mir_type_of(left_local):")).to_equal(false)
expect(mir_expr_source.contains("if val right_type = self.local_mir_type_of(right_local):")).to_equal(false)
expect(mir_expr_source).to_contain("val binop_left_ty = binop_left_ty_opt.unwrap()")
expect(mir_expr_source).to_contain("val binop_right_ty = binop_right_ty_opt.unwrap()")
expect(mir_expr_source.contains("if val found_base_type = base_type:")).to_equal(false)
expect(mir_expr_source).to_contain("if base_type != nil:\n            len_symbol = self.len_runtime_symbol_for_hir_type(base_type)")
expect(mir_stmt_source).to_contain("val expr_disc = mir_hir_stmt_kind_disc(HirStmtKind.Expr(fallback_expr))")
expect(mir_stmt_source).to_contain("if mir_hir_stmt_kind_disc(stmt_kind_value) == expr_disc:")
expect(mir_stmt_source).to_contain("val assign_disc = mir_hir_stmt_kind_disc(HirStmtKind.Assign(fallback_expr, nil, fallback_expr))")
expect(mir_stmt_source).to_contain("val target_t: HirExpr = assign_target")
expect(mir_stmt_source).to_contain("val value_t: HirExpr = assign_value")
expect(mir_stmt_source).to_contain("val field_disc = rt_enum_discriminant(HirExprKind.Field(nil_expr, \"\", nil))")
expect(mir_stmt_source).to_contain("if rt_enum_discriminant(target_kind) == field_disc:")
expect(mir_stmt_source.contains("case Field(base, field, resolved):")).to_equal(false)
```

</details>

#### predispatches struct-shadowed variants in return inference

- predispatches struct-shadowed variants in return inference
   - Expected: source does not contain `match e.kind:\n            case ExprKind.Return(value):`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("predispatches struct-shadowed variants in return inference")
val source = read_source("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val mir_source = read_source("src/compiler/50.mir/_MirLowering/module_lowering.spl")

expect(source).to_contain("if rt_enum_discriminant(expr_kind) == 1138084884:  # hash(\"Block\")")
expect(source).to_contain("if rt_enum_discriminant(expr_kind) == 21232742:  # hash(\"Field\")")
expect(source).to_contain("hir_module_phase_probe(\"return-scan:function:\" + fn_decl.name)")
expect(source).to_contain("hir_module_phase_probe(\"return-scan:ExprKind.Block\")")
expect(source).to_contain("hir_module_phase_probe(\"return-scan:ExprKind.Field\")")
expect(source).to_contain("hir_module_phase_probe(\"return-scan:ExprKind.If\")")
expect(source).to_contain("hir_module_phase_probe(\"return-scan:StmtKind.Expr\")")
expect(source).to_contain("if rt_enum_discriminant(stmt_kind) == expr_disc:")
expect(source).to_contain("val expr_t: Expr = expr")
expect(source).to_contain("case ExprKind.If(cond, then_, else_):")
expect(source).to_contain("return self.scan_ast_block_for_returns(block, params)")
expect(source).to_contain("return self.scan_ast_expr_for_returns(base, params)")
expect(source).to_contain("val then_t: Block = then_")
expect(source).to_contain("val else_t: Block? = else_")
expect(source).to_contain("val cond_t: Expr = cond")
expect(source).to_contain("merge_return_scan(self.scan_ast_expr_for_returns(cond_t, params), self.scan_ast_block_for_returns(then_t, params))")
expect(source.contains("match e.kind:\n            case ExprKind.Return(value):")).to_equal(false)
expect(mir_source).to_contain("val expr_stmt_disc = rt_enum_discriminant(HirStmtKind.Expr(nil_expr))")
expect(mir_source).to_contain("val stmt_disc = rt_enum_discriminant(stmt_kind)")
expect(mir_source).to_contain("if stmt_disc == expr_stmt_disc:")
expect(mir_source).to_contain("eprint(\"[mir-prescan] HirStmtKind.Expr\")")
expect(mir_source).to_contain("val expr_t: HirExpr = expr")
expect(mir_source).to_contain("val let_disc = rt_enum_discriminant(HirStmtKind.Let(SymbolId(id: -1), nil_type, nil_expr))")
expect(mir_source).to_contain("if stmt_disc == let_disc:")
expect(mir_source).to_contain("val init_t: HirExpr = init")
expect(mir_source).to_contain("val assign_disc = rt_enum_discriminant(HirStmtKind.Assign(nil_expr, HirAssignOp.Add, nil_expr))")
expect(mir_source).to_contain("if stmt_disc == assign_disc:")
expect(mir_source).to_contain("val value_t: HirExpr = value")
expect(mir_source).to_contain("val stmt_block_disc = rt_enum_discriminant(HirStmtKind.Block(empty_block))")
expect(mir_source).to_contain("if stmt_disc == stmt_block_disc:")
expect(mir_source).to_contain("val block_t: HirBlock = inner_block")
expect(mir_source).to_contain("val block_disc = rt_enum_discriminant(HirExprKind.Block(HirBlock(stmts: [], has: false, value: nil_expr, span: nil_span)))")
expect(mir_source).to_contain("eprint(\"[mir-prescan] HirExprKind.Block\")")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR statement dispatch source.
- HIR statement dispatch source

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
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c6a2f09ae8aac55be78497babe562588742dde4cdd3624740bfce75c348dd79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c6a2f09ae8aac55be78497babe562588742dde4cdd3624740bfce75c348dd79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c6a2f09ae8aac55be78497babe562588742dde4cdd3624740bfce75c348dd79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses runtime discriminants before struct-shadowed Expr dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares runtime tags for bootstrap statement predispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unwraps initialized Var before local shape registration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
