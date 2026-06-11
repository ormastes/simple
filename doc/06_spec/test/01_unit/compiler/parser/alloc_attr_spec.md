# Alloc Attr Specification

> <details>

<!-- sdn-diagram:id=alloc_attr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=alloc_attr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

alloc_attr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=alloc_attr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alloc Attr Specification

## Scenarios

### #[alloc] attribute

#### parses without error on a function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = create_widget(1, "test")
expect(w.id).to_equal(1)
expect(w.name).to_equal("test")
```

</details>

#### function with #[alloc] returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = create_widget(42, "hello")
expect(w.id).to_equal(42)
```

</details>

#### function with #[alloc] works with new keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = new create_widget(7, "alloc")
expect(w.id).to_equal(7)
expect(w.name).to_equal("alloc")
```

</details>

### #[no_alloc] attribute

#### parses without error on a function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_pure(3, 4)
expect(result).to_equal(7)
```

</details>

#### function with #[no_alloc] returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_pure(100, 200)
expect(result).to_equal(300)
```

</details>

#### function with #[no_alloc] works with new keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = new add_pure(10, 20)
expect(result).to_equal(30)
```

</details>

#### function with #[no_alloc] works without new keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = add_pure(5, 5)
expect(result).to_equal(10)
```

</details>

### combination of alloc attributes and new

#### #[alloc] function called with new returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = new create_widget(99, "combo")
expect(w.id).to_equal(99)
expect(w.name).to_equal("combo")
```

</details>

#### plain function without attributes still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = plain_fn(5)
expect(result).to_equal(10)
```

</details>

#### plain function works with new

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = new plain_fn(8)
expect(result).to_equal(16)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/alloc_attr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- #[alloc] attribute
- #[no_alloc] attribute
- combination of alloc attributes and new

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
