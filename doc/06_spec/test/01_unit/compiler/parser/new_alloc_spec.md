# New Alloc Specification

> <details>

<!-- sdn-diagram:id=new_alloc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=new_alloc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

new_alloc_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=new_alloc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# New Alloc Specification

## Scenarios

### new keyword parsing

#### new expr (default allocator)

#### parses new before constructor call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = new Point(x: 1, y: 2)
expect(p.x).to_equal(1)
expect(p.y).to_equal(2)
```

</details>

#### parses new before function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = new add(3, 4)
expect(result).to_equal(7)
```

</details>

#### parses new before factory function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = new make_point(5, 6)
expect(p.x).to_equal(5)
```

</details>

#### new() expr (type pool)

#### parses new() before constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = new() Point(x: 10, y: 20)
expect(p.x).to_equal(10)
```

</details>

#### parses new() before function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = new() add(100, 200)
expect(result).to_equal(300)
```

</details>

#### new(allocator) expr (explicit allocator)

#### parses new(alloc) before constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alloc = 99
val p = new(alloc) Point(x: 30, y: 40)
expect(p.x).to_equal(30)
```

</details>

#### parses new(alloc) before function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alloc = 99
val result = new(alloc) add(50, 60)
expect(result).to_equal(110)
```

</details>

#### new in various expression positions

#### new result assigned to val

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = new add(1, 1)
expect(x).to_equal(2)
```

</details>

#### new result used in arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = new add(2, 3) + 10
expect(x).to_equal(15)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/new_alloc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- new keyword parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
