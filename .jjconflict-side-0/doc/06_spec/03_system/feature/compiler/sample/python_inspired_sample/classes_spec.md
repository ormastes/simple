# Classes (Python-Inspired Sample)

> Tests compilation of class definitions inspired by Python patterns including fields, methods, and static methods. Verifies that Simple's composition-based class model correctly compiles constructs familiar to Python developers.

<!-- sdn-diagram:id=classes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=classes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

classes_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=classes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Classes (Python-Inspired Sample)

Tests compilation of class definitions inspired by Python patterns including fields, methods, and static methods. Verifies that Simple's composition-based class model correctly compiles constructs familiar to Python developers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of class definitions inspired by Python patterns including
fields, methods, and static methods. Verifies that Simple's composition-based
class model correctly compiles constructs familiar to Python developers.

## Scenarios

### Classes

#### class definition

#### defines a simple class with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Point:
    x: i64
    y: i64
val p = Point(x: 3, y: 4)
expect p.x == 3
expect p.y == 4
```

</details>

#### instance methods

#### defines and calls immutable method

1. fn area
2. expect rect area


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Rectangle:
    width: i64
    height: i64

    fn area() -> i64:
        self.width * self.height

val rect = Rectangle(width: 5, height: 3)
expect rect.area() == 15
```

</details>

#### mutable methods

#### modifies instance with me method

1. me increment
2. var c = Counter
3. c increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    value: i64

    me increment():
        self.value = self.value + 1

var c = Counter(value: 0)
c.increment()
expect c.value == 1
```

</details>

#### static methods

#### creates instance via static factory

1. static fn unit
2. Circle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Circle:
    radius: f64

impl Circle:
    static fn unit() -> Circle:
        Circle(radius: 1.0)

val c = Circle.unit()
expect c.radius == 1.0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
