# Async Await Eager Value Specification

> <details>

<!-- sdn-diagram:id=async_await_eager_value_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_await_eager_value_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_await_eager_value_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_await_eager_value_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Await Eager Value Specification

## Scenarios

### await on async fn (B2 eager-async)

#### zero-arg async fn

#### returns the body value, not NIL/3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got = run_await_42()
expect(got).to_equal(42)
```

</details>

#### async fn with args

#### returns the computed value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got = run_await_add()
expect(got).to_equal(42)
```

</details>

#### await inside expression position

#### awaited value usable in arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got = run_await_42() + 8
expect(got).to_equal(50)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- await on async fn (B2 eager-async)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
