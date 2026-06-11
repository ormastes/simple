# Linalg Specification

> <details>

<!-- sdn-diagram:id=linalg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linalg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linalg_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linalg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linalg Specification

## Scenarios

### Linear Algebra

#### matrix operations

#### computes determinant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

<details>
<summary>Advanced: computes matrix inverse</summary>

#### computes matrix inverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>


</details>

#### solves linear system

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### advanced operations

#### computes eigenvalues

1. expect la supports eigenvalues


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val la = MockLinAlg()
expect la.supports_eigenvalues()
```

</details>

#### computes SVD

1. expect la supports svd


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val la = MockLinAlg()
expect la.supports_svd()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ml/linalg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linear Algebra

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
