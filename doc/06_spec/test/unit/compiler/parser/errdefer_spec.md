# Errdefer Specification

> <details>

<!-- sdn-diagram:id=errdefer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=errdefer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

errdefer_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=errdefer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Errdefer Specification

## Scenarios

### Errdefer

### parsing

#### parses errdefer statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = parse_one_statement("errdefer cleanup()")
expect(stmt_get_tag(stmt)).to_equal(STMT_ERRDEFER)
expect(expr_get_tag(stmt_get_expr(stmt))).to_equal(EXPR_CALL)
```

</details>

#### parses defer statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt = parse_one_statement("defer cleanup()")
expect(stmt_get_tag(stmt)).to_equal(STMT_DEFER)
expect(expr_get_tag(stmt_get_expr(stmt))).to_equal(EXPR_CALL)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/errdefer_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Errdefer
- parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
