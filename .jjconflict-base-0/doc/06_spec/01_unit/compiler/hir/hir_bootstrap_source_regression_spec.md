# Hir Bootstrap Source Regression Specification

> Tests covering HIR bootstrap source regressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Bootstrap Source Regression Specification

## Scenarios

### HIR bootstrap source regressions

#### constructs lowering collections with explicit stage4 types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs lowering collections with explicit stage4 types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs lowering collections with explicit stage4 types")
val types = file_text("src/compiler/20.hir/hir_lowering/types.spl")
expect(types).to_contain("val empty_errors: [LoweringError] = []")
expect(types).to_contain("val empty_loaded_modules: [text] = []")
expect(types).to_contain("val empty_modules_by_name: Dict<text, Module> = {}")
```

</details>

#### extracts named types before constructing other enum payload exemplars

- extracts named types before constructing other enum payload exemplars


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts named types before constructing other enum payload exemplars")
val types = file_text("src/compiler/20.hir/hir_lowering/types.spl")
val parser_types = file_text("src/compiler/10.frontend/parser_types_expr.spl")
val named_return = types.index_of("return HirType(kind: named_kind, span: lt.span)")
val optional_exemplar = types.index_of("val d_opt: i64 = hir_type_kind_disc(TypeKind.Optional(lt))")
expect(parser_types).to_contain("fn parser_type_kind_named_name(kind: TypeKind) -> text:")
expect(parser_types).to_contain("fn parser_type_kind_named_args(kind: TypeKind) -> [Type]:")
expect(parser_types.contains("compiler.hir")).to_be(false)
expect(types).to_contain("val nm: text = parser_type_kind_named_name(lt_kind)")
expect(types).to_contain("val nargs: [Type] = parser_type_kind_named_args(lt_kind)")
expect(types).to_contain("internal: failed to extract named type")
expect(types.contains("rt_enum_payload(value: TypeKind)")).to_be(false)
expect(types.contains("case TypeKind.Named(name, args):")).to_be(false)
expect(named_return).to_be_greater_than(-1)
expect(optional_exemplar).to_be_greater_than(named_return)
```

</details>

#### uses the runtime discriminant for struct-named type variants

- uses the runtime discriminant for struct-named type variants
   - Expected: types does not contain `fn hir_type_kind_disc(k: TypeKind) -> i64:\n    match k:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the runtime discriminant for struct-named type variants")
val types = file_text("src/compiler/20.hir/hir_lowering/types.spl")
expect(types).to_contain("fn hir_type_kind_disc(k: TypeKind) -> i64:\n    rt_enum_discriminant(k)")
expect(types.contains("fn hir_type_kind_disc(k: TypeKind) -> i64:\n    match k:")).to_equal(false)
```

</details>

#### makes HIR diagnostics fatal unless lowering explicitly recovered

- makes HIR diagnostics fatal unless lowering explicitly recovered


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes HIR diagnostics fatal unless lowering explicitly recovered")
val types = file_text("src/compiler/20.hir/hir_lowering/types.spl")
val async_lowering = file_text("src/compiler/20.hir/hir_lowering/async.spl")
val statements = file_text("src/compiler/20.hir/hir_lowering/statements.spl")
val declarations = file_text("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
val trait_impls = file_text("src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl")
val driver = file_text("src/compiler/80.driver/driver.spl")
expect(types).to_contain("kind: LoweringErrorKind.Recovered")
expect(types).to_contain("self.recovered(\"Result type expects 2 type arguments\"")
expect(types).to_contain("name == \"Any\" or (name == \"Option\" and hir_args.len() == 0)")
expect(types).to_contain("self.error(\"Dict type expects 2 type arguments\"")
expect(types).to_contain("self.error(\"unresolved type: {name}\"")
expect(async_lowering).to_contain("self.recovered(\"async: {detail.message}")
expect(statements).to_contain("self.error(\"tuple destructure arity mismatch")
expect(declarations).to_contain("self.error(\"generic functions are not supported")
expect(trait_impls).to_contain("self.error(\"generic struct/class methods are not supported")
expect(driver).to_contain("err.kind == LoweringErrorKind.Recovered")
expect(driver.contains("fn _hir_lowering_error_is_fatal")).to_be(false)
```

</details>

#### uses the runtime discriminant for struct-named expression variants

- uses the runtime discriminant for struct-named expression variants
   - Expected: expressions does not contain `fn hir_expr_kind_disc(k: ExprKind) -> i64:\n    match k:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the runtime discriminant for struct-named expression variants")
val expressions = file_text("src/compiler/20.hir/hir_lowering/expressions.spl")
expect(expressions).to_contain("fn hir_expr_kind_disc(k: ExprKind) -> i64:\n    rt_enum_discriminant(k)")
expect(expressions.contains("fn hir_expr_kind_disc(k: ExprKind) -> i64:\n    match k:")).to_equal(false)
expect(expressions.index_of("case ExprKind.Call(callee, args):")).to_be_less_than(expressions.index_of("val kind_disc_v: i64"))
expect(expressions.index_of("case ExprKind.NilLit:")).to_be_greater_than(expressions.index_of("case ExprKind.Call(callee, args):"))
```

</details>

#### does not use ParserModule aliases in item lowering

- does not use ParserModule aliases in item lowering
   - Expected: module_lowering does not contain `ParserModule`
   - Expected: lowering_helpers does not contain `ParserModule`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not use ParserModule aliases in item lowering")
val module_lowering = file_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val lowering_helpers = file_text("src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl")
expect(module_lowering.contains("ParserModule")).to_equal(false)
expect(lowering_helpers.contains("ParserModule")).to_equal(false)
```

</details>

#### keeps exists-check index lowering before boolean inference

- keeps exists-check index lowering before boolean inference
   - Expected: expressions contains `HirExprKind.ExistsCheck(indexed)`
   - Expected: expressions does not contain `var symbol_type: HirType? = nil`
   - Expected: expressions does not contain `symbol_type = bootstrap_builtin_signature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps exists-check index lowering before boolean inference")
val expressions = file_text("src/compiler/20.hir/hir_lowering/expressions.spl")
expect(expressions.contains("HirExprKind.ExistsCheck(indexed)")).to_equal(true)
expect(expressions.contains("var symbol_type: HirType? = nil")).to_equal(false)
expect(expressions.contains("symbol_type = bootstrap_builtin_signature")).to_equal(false)
expect(expressions).to_contain("val symbol_type = if is_bootstrap_builtin")
```

</details>

#### imports custom primitive helpers from the frontend owner module

- imports custom primitive helpers from the frontend owner module
   - Expected: type_lowering does not contain `compiler.core.types.{custom_primitive`
   - Expected: module_lowering does not contain `compiler.core.{TYPE_VOID, TYPE_BOOL, TYPE_I64, TYPE_TEXT, custom_primitive`
   - Expected: declaration_lowering does not contain `compiler.core.{TYPE_VOID, TYPE_BOOL, TYPE_I64, TYPE_TEXT, custom_primitive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("imports custom primitive helpers from the frontend owner module")
val type_lowering = file_text("src/compiler/20.hir/hir_lowering/types.spl")
val module_lowering = file_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val declaration_lowering = file_text("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
expect(type_lowering.contains("compiler.core.types.{custom_primitive")).to_equal(false)
expect(module_lowering.contains("compiler.core.{TYPE_VOID, TYPE_BOOL, TYPE_I64, TYPE_TEXT, custom_primitive")).to_equal(false)
expect(declaration_lowering.contains("compiler.core.{TYPE_VOID, TYPE_BOOL, TYPE_I64, TYPE_TEXT, custom_primitive")).to_equal(false)
expect(type_lowering).to_contain("compiler.frontend.core.types.{custom_primitive_bind_symbol, custom_primitive_is_name}")
```

</details>

#### keeps statement payload extraction single-assignment

- keeps statement payload extraction single-assignment
   - Expected: statements does not contain `var v_name: text = ""`
   - Expected: statements does not contain `var v_type: Type? = nil`
   - Expected: statements does not contain `var v_init: Expr = sk_dummy`
   - Expected: statements does not contain `var vr_name: text = ""`
   - Expected: statements does not contain `var vr_type: Type? = nil`
   - Expected: statements does not contain `var vr_init: Expr? = nil`
   - Expected: statements does not contain `var rt_val: Expr? = nil`
   - Expected: statements does not contain `var as_op: AssignOp? = nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps statement payload extraction single-assignment")
val statements = file_text("src/compiler/20.hir/hir_lowering/statements.spl")

expect(statements.contains("var v_name: text = \"\"")).to_equal(false)
expect(statements.contains("var v_type: Type? = nil")).to_equal(false)
expect(statements.contains("var v_init: Expr = sk_dummy")).to_equal(false)
expect(statements.contains("var vr_name: text = \"\"")).to_equal(false)
expect(statements.contains("var vr_type: Type? = nil")).to_equal(false)
expect(statements.contains("var vr_init: Expr? = nil")).to_equal(false)
expect(statements.contains("var rt_val: Expr? = nil")).to_equal(false)
expect(statements.contains("var as_op: AssignOp? = nil")).to_equal(false)
expect(statements).to_contain("val v_type = match stmt_kind_value")
expect(statements).to_contain("val vr_type = match stmt_kind_value")
expect(statements).to_contain("val vr_init = match stmt_kind_value")
expect(statements).to_contain("val rt_val = match stmt_kind_value")
expect(statements).to_contain("val as_op = match stmt_kind_value")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR bootstrap source regressions.
- HIR bootstrap source regressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `1ec82f613c9b421d051198625e4536f1a3ddd5dfd69628845d0907d972329b70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1ec82f613c9b421d051198625e4536f1a3ddd5dfd69628845d0907d972329b70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1ec82f613c9b421d051198625e4536f1a3ddd5dfd69628845d0907d972329b70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs lowering collections with explicit stage4 types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts named types before constructing other enum payload exemplars' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/hir_bootstrap_source_regression_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the runtime discriminant for struct-named type variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
