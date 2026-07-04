# Constructor Specification

> 1. check

<!-- sdn-diagram:id=constructor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=constructor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

constructor_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=constructor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Constructor Specification

## Scenarios

### Module-Level Constructors

#### Direct construction works (PRIMARY METHOD)

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(5, 6)
check(p.x == 5)
check(p.y == 6)
```

</details>

#### Direct construction with named parameters

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(x: 7, y: 8)
check(p.x == 7)
check(p.y == 8)
```

</details>

#### fn new() is implicitly static at module level

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.new(3, 4)
check(p.x == 3)
check(p.y == 4)
```

</details>

#### fn create() is implicitly static

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = Config.create(42)
check(cfg.value == 42)
```

</details>

#### fn default() is implicitly static

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val settings = Settings.default()
check(settings.enabled == true)
```

</details>

#### fn from_* is implicitly static

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point.from_tuple((10, 20))
check(p.x == 10)
check(p.y == 20)
```

</details>

#### static fn with_* works as factory

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = Builder.with_name("test")
check(b.name == "test")
```

</details>

#### Explicit static keyword still works

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Rectangle.new(10, 20)
check(r.width == 10)
check(r.height == 20)
```

</details>

#### Instance methods still get implicit self

1. check
2. c increment
3. check
4. c increment
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Counter.new()
check(c.get_count() == 0)
c.increment()
check(c.get_count() == 1)
c.increment()
check(c.get_count() == 2)
```

</details>

#### Direct construction and new() can coexist

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Point(1, 2)          # Direct
val p2 = Point.new(3, 4)      # Via new()
check(p1.x + p2.x == 4)
check(p1.y + p2.y == 6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/constructor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module-Level Constructors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
