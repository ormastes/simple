# Bidir Type Check Specification

> <details>

<!-- sdn-diagram:id=bidir_type_check_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bidir_type_check_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bidir_type_check_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bidir_type_check_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bidir Type Check Specification

## Scenarios

### Bidir Type Check

#### keeps bidirectional inference modes available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_bidir_source("src/compiler/30.types/bidirectional_types.spl")

expect(source).to_contain("enum InferMode")
expect(source).to_contain("Synthesize")
expect(source).to_contain("Check")
```

</details>

#### keeps bidirectional expression inference entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_bidir_source("src/compiler/30.types/bidirectional_inferencer.spl")

expect(source).to_contain("me infer_expr(expr: BidirHirExpr, mode: InferMode) -> HirType")
expect(source).to_contain("me check_expr(expr: BidirHirExpr, expected: HirType) -> HirType")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/bidir_type_check_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bidir Type Check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
