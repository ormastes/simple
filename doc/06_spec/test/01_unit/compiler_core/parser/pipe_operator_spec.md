# Pipe Operator Specification

> <details>

<!-- sdn-diagram:id=pipe_operator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pipe_operator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pipe_operator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pipe_operator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pipe Operator Specification

## Scenarios

### Pipe operator |>

#### basic pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 |> double
expect(result).to_equal(10)
```

</details>

#### pipe with extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 |> add(2)
expect(result).to_equal(3)
```

</details>

#### chained pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 |> double |> triple
expect(result).to_equal(12)
```

</details>

#### pipe to add1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 |> add1
expect(result).to_equal(11)
```

</details>

#### pipe chain three

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 |> add1 |> double |> triple
expect(result).to_equal(12)
```

</details>

#### pipe to lambda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 |> (\x: x * 3)
expect(result).to_equal(15)
```

</details>

#### pipe to placeholder lambda in parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 |> (_1 * 3)
expect(result).to_equal(15)
```

</details>

#### pipe to composed function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = double >> triple
val result = 2 |> f
expect(result).to_equal(12)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/parser/pipe_operator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Pipe operator |>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
