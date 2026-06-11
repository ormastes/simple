# Dim Constraints Specification

> <details>

<!-- sdn-diagram:id=dim_constraints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dim_constraints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dim_constraints_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dim_constraints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dim Constraints Specification

## Scenarios

### Dim Constraints

#### keeps dimension expression constructors available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_dim_source("src/compiler/20.hir/hir_types.spl")

expect(source).to_contain("enum DimExprKind")
expect(source).to_contain("static fn literal(value: i64, span: Span) -> DimExpr")
expect(source).to_contain("static fn dynamic(span: Span) -> DimExpr")
```

</details>

#### keeps dimension solver and error formatting available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val solver_source = read_dim_source("src/compiler/30.types/dim_constraints.spl")
val types_source = read_dim_source("src/compiler/30.types/dim_constraints_types.spl")

expect(solver_source).to_contain("struct DimSolver")
expect(solver_source).to_contain("fn format_shape(dims: [DimExpr]) -> text")
expect(types_source).to_contain("enum DimErrorKind")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type_inference/dim_constraints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Dim Constraints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
