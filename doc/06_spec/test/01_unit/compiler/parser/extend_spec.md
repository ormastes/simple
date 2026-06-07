# Extend Specification

> <details>

<!-- sdn-diagram:id=extend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=extend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

extend_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=extend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Extend Specification

## Scenarios

### extend type declarations

#### can call extended method (magnitude)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(x: 3, y: 4)
val mag = Point__magnitude(p)
expect(mag).to_equal(25)
```

</details>

#### can call extended method that returns struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(x: 1, y: 2)
val p2 = Point__translate(p, 10, 20)
expect(p2.x).to_equal(11)
expect(p2.y).to_equal(22)
```

</details>

#### can call extended static method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val origin = Point__zero()
expect(origin.x).to_equal(0)
expect(origin.y).to_equal(0)
```

</details>

#### distance between two points

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Point(x: 0, y: 0)
val b = Point(x: 3, y: 4)
val dist = Point__distance(a, b)
expect(dist).to_equal(25)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/extend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- extend type declarations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
