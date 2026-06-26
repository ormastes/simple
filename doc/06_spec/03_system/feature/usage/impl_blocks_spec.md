# Implementation Blocks Specification

> Implementation blocks (`impl`) provide a flexible way to define methods for types outside of the type definition. This enables separation of concerns, method organization, and extension of types in different modules without modifying the original definition.

<!-- sdn-diagram:id=impl_blocks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=impl_blocks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

impl_blocks_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=impl_blocks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Implementation Blocks Specification

Implementation blocks (`impl`) provide a flexible way to define methods for types outside of the type definition. This enables separation of concerns, method organization, and extension of types in different modules without modifying the original definition.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #830-835 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/impl_blocks_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Implementation blocks (`impl`) provide a flexible way to define methods for types outside
of the type definition. This enables separation of concerns, method organization, and
extension of types in different modules without modifying the original definition.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Impl Block | Collection of methods for a type |
| Instance Method | Methods that receive self as implicit parameter |
| Static Method | Methods that don't receive self |
| Method Organization | Grouping related behavior in impl blocks |

## Behavior

- Methods in impl blocks are part of the type's interface
- Impl blocks can be placed in any module or location
- Multiple impl blocks for the same type are merged
- Static methods are called with type name prefix
- Instance methods use dot notation on values

## Scenarios

### Implementation Blocks - Basic

#### defines methods in impl block

1. expect p get x


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(x: 5, y: 10)
expect p.get_x() == 5
```

</details>

#### defines multiple methods

1. expect r area
2. expect r perimeter


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rectangle(width: 4, height: 5)
expect r.area() == 20
expect r.perimeter() == 18
```

</details>

### Implementation Blocks - Static Methods

#### uses static factory method

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Point.origin()
expect p1.x == 0
expect p1.y == 0

val p2 = Point.from_coords(3, 4)
expect p2.x == 3
expect p2.y == 4
```

</details>

### Implementation Blocks - Instance Methods

#### defines immutable methods

1. expect c area
2. expect c circumference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Circle(radius: 5.0)
# Approximate equality due to floating point
expect c.area() > 78.0
expect c.circumference() > 31.0
```

</details>

#### defines mutable methods

1. c increment
2. c decrement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Counter(count: 0)
c.increment()
expect c.count == 1
c.decrement()
expect c.count == 0
```

</details>

### Implementation Blocks - Mixed Methods

#### mixes static and instance methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Temperature.from_fahrenheit(32.0)
# Approximately 0 celsius
expect t.celsius > -1.0
expect t.celsius < 1.0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
