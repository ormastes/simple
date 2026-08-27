# Hir Expression Shared Binding Contract Specification

> Tests covering HIR expression strict shared bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Expression Shared Binding Contract Specification

## Scenarios

### HIR expression strict shared bindings

#### resolves field symbols without optional zero payloads

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves field symbols without optional zero payloads
   - Expected: source does not contain `val else_block: HirBlock? = match else_:`
   - Expected: source does not contain `if val fld_base_sym = fld_module_base_sym:`
   - Expected: source does not contain `if val fld_base_sym = fld_base_sym_opt:`
   - Expected: source does not contain `if fld_base_symbol != nil:`
   - Expected: source does not contain `val fld_field_type: HirType? = match fld_base_sym_opt:`
   - Expected: source does not contain `var fld_module_base_sym: SymbolId? = nil`
   - Expected: source does not contain `var module_callable: SymbolId? = nil`
   - Expected: source does not contain `var fld_tuple_elem_type: HirType? = nil`
   - Expected: source does not contain `var fld_tuple_base_sym: SymbolId? = nil`
   - Expected: source does not contain `var fld_field_type: HirType? = nil`
   - Expected: source does not contain `var fld_base_sym_opt: SymbolId? = nil`
   - Expected: source does not contain `var fld_owner_sym_opt: SymbolId? = nil`
   - Expected: source does not contain `var rest_symbol: SymbolId? = nil`
   - Expected: source does not contain `var else_block: HirBlock? = nil`
   - Expected: source does not contain `var yv: HirExpr? = nil`
   - Expected: source does not contain `var rstart: HirExpr? = nil`
   - Expected: source does not contain `var rend: HirExpr? = nil`
   - Expected: source does not contain `var rstep: HirExpr? = nil`
   - Expected: source does not contain `var hir_payload: HirPatternPayload? = nil`
   - Expected: source does not contain `var pstart: HirExpr? = nil`
   - Expected: source does not contain `var pend: HirExpr? = nil`
   - Expected: source does not contain `var combined: HirExpr? = nil`
   - Expected: source does not contain `var combined2: HirExpr? = nil`
   - Expected: source does not contain `var combined3: HirExpr? = nil`
   - Expected: source does not contain `var else_opt: HirBlock? = nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("resolves field symbols without optional zero payloads")
val source = file_read("src/compiler/20.hir/hir_lowering/expressions.spl")

expect(source).to_contain("fn _hir_expr_symbol_or_invalid(kind: HirExprKind) -> SymbolId:")
expect(source).to_contain("case _: SymbolId(id: -1)")
expect(source).to_contain("me field_module_callable(module_name: text, field_name: text) -> SymbolId?:")
expect(source).to_contain("me field_tuple_element_type(base_kind: HirExprKind, index: i64) -> HirType?:")
expect(source).to_contain("me field_type_for_base(base_symbol: SymbolId, field_name: text) -> HirType?:")
expect(source).to_contain("me combine_pattern_conditions(conditions: [HirExpr], count: i64, op: HirBinOp, span: Span) -> HirExpr:")
expect(source).to_contain("if e == nil:")
expect(source).to_contain("missing AST expression during HIR lowering")
expect(source).to_contain("kind: HirExprKind.Error,")
expect(source).to_contain("val kind_disc_dummy = Expr(kind: ExprKind.NilLit, span: e.span)")
expect(source).to_contain("kind_disc_v == hir_expr_kind_disc(ExprKind.MethodCall(kind_disc_dummy, \"\", []))")
expect(source).to_contain("kind_disc_v == hir_expr_kind_disc(ExprKind.If(kind_disc_dummy, Block(stmts: [], span: e.span), nil))")
expect(source).to_contain("val rest_symbol: SymbolId? = match rest:")
expect(source).to_contain("if val else_block_src = else_:")
expect(source).to_contain("HirExprKind.If(hir_cond, hir_then, self.lower_hir_block(else_block_src))")
expect(source.contains("val else_block: HirBlock? = match else_:")).to_equal(false)
expect(source).to_contain("val hir_payload: HirPatternPayload? = match payload:")
expect(source).to_contain("val else_opt: HirBlock? = else_block")
expect(source).to_contain("val fld_base_sym = _hir_expr_symbol_or_invalid(fld_lowered_base.kind)")
expect(source).to_contain("if fld_base_sym.is_valid():")
expect(source).to_contain("if val fld_base_symbol = self.symbols.get_symbol_raw(fld_base_sym.id):")
expect(source).to_contain("val fld_field_type: HirType? = if fld_base_sym.is_valid():")
expect(source).to_contain("self.field_type_for_base_raw(fld_base_sym.id, fld_name_t)")
expect(source.contains("if val fld_base_sym = fld_module_base_sym:")).to_equal(false)
expect(source.contains("if val fld_base_sym = fld_base_sym_opt:")).to_equal(false)
expect(source.contains("if fld_base_symbol != nil:")).to_equal(false)
expect(source.contains("val fld_field_type: HirType? = match fld_base_sym_opt:")).to_equal(false)
expect(source.contains("var fld_module_base_sym: SymbolId? = nil")).to_equal(false)
expect(source.contains("var module_callable: SymbolId? = nil")).to_equal(false)
expect(source.contains("var fld_tuple_elem_type: HirType? = nil")).to_equal(false)
expect(source.contains("var fld_tuple_base_sym: SymbolId? = nil")).to_equal(false)
expect(source.contains("var fld_field_type: HirType? = nil")).to_equal(false)
expect(source.contains("var fld_base_sym_opt: SymbolId? = nil")).to_equal(false)
expect(source.contains("var fld_owner_sym_opt: SymbolId? = nil")).to_equal(false)
expect(source.contains("var rest_symbol: SymbolId? = nil")).to_equal(false)
expect(source.contains("var else_block: HirBlock? = nil")).to_equal(false)
expect(source.contains("var yv: HirExpr? = nil")).to_equal(false)
expect(source.contains("var rstart: HirExpr? = nil")).to_equal(false)
expect(source.contains("var rend: HirExpr? = nil")).to_equal(false)
expect(source.contains("var rstep: HirExpr? = nil")).to_equal(false)
expect(source.contains("var hir_payload: HirPatternPayload? = nil")).to_equal(false)
expect(source.contains("var pstart: HirExpr? = nil")).to_equal(false)
expect(source.contains("var pend: HirExpr? = nil")).to_equal(false)
expect(source.contains("var combined: HirExpr? = nil")).to_equal(false)
expect(source.contains("var combined2: HirExpr? = nil")).to_equal(false)
expect(source.contains("var combined3: HirExpr? = nil")).to_equal(false)
expect(source.contains("var else_opt: HirBlock? = nil")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR expression strict shared bindings.
- HIR expression strict shared bindings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `f7b2ad7601bf67e0f16ae604ab07e9f13ee9f713090dc35dcdd6199c129d9681`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7b2ad7601bf67e0f16ae604ab07e9f13ee9f713090dc35dcdd6199c129d9681`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7b2ad7601bf67e0f16ae604ab07e9f13ee9f713090dc35dcdd6199c129d9681`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves field symbols without optional zero payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
