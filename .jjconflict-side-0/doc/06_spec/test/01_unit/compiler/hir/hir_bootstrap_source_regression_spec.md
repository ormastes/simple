# Hir Bootstrap Source Regression Specification

> <details>

<!-- sdn-diagram:id=hir_bootstrap_source_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hir_bootstrap_source_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hir_bootstrap_source_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hir_bootstrap_source_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Bootstrap Source Regression Specification

## Scenarios

### HIR bootstrap source regressions

#### does not use ParserModule aliases in item lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_lowering = file_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")
val lowering_helpers = file_text("src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl")
expect(module_lowering.contains("ParserModule")).to_equal(false)
expect(lowering_helpers.contains("ParserModule")).to_equal(false)
```

</details>

#### keeps exists-check index lowering before boolean inference

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expressions = file_text("src/compiler/20.hir/hir_lowering/expressions.spl")
expect(expressions.contains("HirExprKind.ExistsCheck(indexed)")).to_equal(true)
expect(expressions.contains("var symbol_type: HirType? = nil")).to_equal(false)
expect(expressions.contains("symbol_type = bootstrap_builtin_signature")).to_equal(false)
expect(expressions).to_contain("val symbol_type = if is_bootstrap_builtin")
```

</details>

#### imports custom primitive helpers from the frontend owner module

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HIR bootstrap source regressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
