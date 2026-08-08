# Ops Specification

> <details>

<!-- sdn-diagram:id=ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ops_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ops Specification

## Scenarios

### Ops

#### keeps arithmetic and comparison operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_ops_source()

expect(source).to_contain("fn val_add(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_sub(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_mul(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_div(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_mod(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_eq(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_lt(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_gteq(a: i64, b: i64) -> i64")
```

</details>

#### keeps logical unary and dispatch operations available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = interpreter_ops_source()

expect(source).to_contain("fn val_and(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_or(a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_not(a: i64) -> i64")
expect(source).to_contain("fn val_negate(a: i64) -> i64")
expect(source).to_contain("fn val_binary_op(op: i64, a: i64, b: i64) -> i64")
expect(source).to_contain("fn val_unary_op(op: i64, a: i64) -> i64")
expect(source).to_contain("fn val_compound_op(op: i64, a: i64, b: i64) -> i64")
expect(source).to_contain("fn ops_get_error() -> text")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
