# R1 Class In It Specification

> <details>

<!-- sdn-diagram:id=r1_class_in_it_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=r1_class_in_it_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

r1_class_in_it_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=r1_class_in_it_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# R1 Class In It Specification

## Scenarios

### R1 nested class definitions

#### instantiates a class defined inside the it block

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point:
    x: i32
    y: i32

val p = Point(x: 7, y: 11)
expect p.x == 7
expect p.y == 11
```

</details>

#### calls a static factory on a class defined inside the it block

1. static fn from
2. IP


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class IP:
    value: text

    static fn from(s: text) -> IP:
        IP(value: s)

val addr = IP.from("127.0.0.1")
expect addr.value == "127.0.0.1"
```

</details>

#### supports two it-blocks declaring the same class name (first wins)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Box:
    v: i32

val b = Box(v: 42)
expect b.v == 42
```

</details>

#### supports two it-blocks declaring the same class name (second occurrence)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The hoist policy keeps the first declaration of `Box` and drops
# this one; the runtime semantics of the BDD interpreter still
# construct `Box(v: 99)` because it walks AST per `it` block.
class Box:
    v: i32

val b = Box(v: 99)
expect b.v == 99
```

</details>

#### handles a class with multiple fields and a method

1. fn area
2. expect r area


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Rect:
    w: i32
    h: i32

    fn area(self) -> i32:
        self.w * self.h

val r = Rect(w: 4, h: 5)
expect r.area() == 20
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/r1_class_in_it_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- R1 nested class definitions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
