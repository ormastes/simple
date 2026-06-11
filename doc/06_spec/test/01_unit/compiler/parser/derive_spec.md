# Derive Specification

> <details>

<!-- sdn-diagram:id=derive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=derive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

derive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=derive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Derive Specification

## Scenarios

### @derive annotation parsing

#### struct with @derive comment can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color(r: 255, g: 128, b: 0)
expect(c.r).to_equal(255)
expect(c.g).to_equal(128)
expect(c.b).to_equal(0)
```

</details>

#### another derived struct works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point2D(x: 3, y: 4)
expect(p.x).to_equal(3)
expect(p.y).to_equal(4)
```

</details>

#### derived struct fields are accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color(r: 0, g: 255, b: 0)
val sum = c.r + c.g + c.b
expect(sum).to_equal(255)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/derive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- @derive annotation parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
