# Contract spec: test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl` and a green Results line.

## Scenarios

### HIR expression strict shared bindings

#### resolves field symbols without optional zero payloads

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves field symbols without optional zero payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
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
expect(source).to_not_contain("val else_block: HirBlock? = match else_:")        expect(source).to_contain("val hir_payload: HirPatternPayload? = match payload:")
expect(source).to_contain("val else_opt: HirBlock? = else_block")
expect(source).to_contain("val fld_base_sym = _hir_expr_symbol_or_invalid(fld_lowered_base.kind)")
expect(source).to_contain("if fld_base_sym.is_valid():")
expect(source).to_contain("if val fld_base_symbol = self.symbols.get_symbol_raw(fld_base_sym.id):")
expect(source).to_contain("val fld_field_type: HirType? = if fld_base_sym.is_valid():")
expect(source).to_contain("self.field_type_for_base_raw(fld_base_sym.id, fld_name_t)")
expect(source).to_not_contain("if val fld_base_sym = fld_module_base_sym:")        expect(source).to_not_contain("if val fld_base_sym = fld_base_sym_opt:")        expect(source).to_not_contain("if fld_base_symbol != nil:")        expect(source).to_not_contain("val fld_field_type: HirType? = match fld_base_sym_opt:")        expect(source).to_not_contain("var fld_module_base_sym: SymbolId? = nil")        expect(source).to_not_contain("var module_callable: SymbolId? = nil")        expect(source).to_not_contain("var fld_tuple_elem_type: HirType? = nil")        expect(source).to_not_contain("var fld_tuple_base_sym: SymbolId? = nil")        expect(source).to_not_contain("var fld_field_type: HirType? = nil")        expect(source).to_not_contain("var fld_base_sym_opt: SymbolId? = nil")        expect(source).to_not_contain("var fld_owner_sym_opt: SymbolId? = nil")        expect(source).to_not_contain("var rest_symbol: SymbolId? = nil")        expect(source).to_not_contain("var else_block: HirBlock? = nil")        expect(source).to_not_contain("var yv: HirExpr? = nil")        expect(source).to_not_contain("var rstart: HirExpr? = nil")        expect(source).to_not_contain("var rend: HirExpr? = nil")        expect(source).to_not_contain("var rstep: HirExpr? = nil")        expect(source).to_not_contain("var hir_payload: HirPatternPayload? = nil")        expect(source).to_not_contain("var pstart: HirExpr? = nil")        expect(source).to_not_contain("var pend: HirExpr? = nil")        expect(source).to_not_contain("var combined: HirExpr? = nil")        expect(source).to_not_contain("var combined2: HirExpr? = nil")        expect(source).to_not_contain("var combined3: HirExpr? = nil")        expect(source).to_not_contain("var else_opt: HirBlock? = nil")
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6b1f246c380af570f5faefcf58662a15673dd3e8efa065836232e6828fed0ec9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b1f246c380af570f5faefcf58662a15673dd3e8efa065836232e6828fed0ec9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b1f246c380af570f5faefcf58662a15673dd3e8efa065836232e6828fed0ec9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/hir_expression_shared_binding_contract_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves field symbols without optional zero payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
