# Compose Operator Specification

> <details>

<!-- sdn-diagram:id=compose_operator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compose_operator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compose_operator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compose_operator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compose Operator Specification

## Scenarios

### Compose operator >>

#### basic compose

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = double >> triple
expect(f(2)).to_equal(12)
```

</details>

#### chained compose

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = add1 >> double >> triple
expect(f(1)).to_equal(12)
```

</details>

#### compose with pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = double >> add1
val result = 5 |> f
expect(result).to_equal(11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/parser/compose_operator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Compose operator >>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
