# Utils Specification

> <details>

<!-- sdn-diagram:id=utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

utils_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utils Specification

## Scenarios

### Utils

#### defines immutable list constructors and predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_list_source()

expect(src).to_contain("enum List<T>:")
expect(src).to_contain("Nil")
expect(src).to_contain("Cons(head: T, tail: List<T>)")
expect(src).to_contain("fn list_empty<T>() -> List<T>:")
expect(src).to_contain("fn list_cons<T>(head: T, tail: List<T>) -> List<T>:")
expect(src).to_contain("fn list_is_empty<T>(l: List<T>) -> bool:")
expect(src).to_contain("case Nil: true")
expect(src).to_contain("case _: false")
```

</details>

#### defines pure list traversal and array conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_list_source()

expect(src).to_contain("fn list_len<T>(l: List<T>) -> i64:")
expect(src).to_contain("case Nil: 0")
expect(src).to_contain("case Cons(_, tail): 1 + list_len(tail)")
expect(src).to_contain("fn list_head<T>(l: List<T>) -> Option<T>:")
expect(src).to_contain("fn list_tail<T>(l: List<T>) -> List<T>:")
expect(src).to_contain("fn list_to_array<T>(l: List<T>) -> [T]:")
expect(src).to_contain("fn list_from_array<T>(arr: [T]) -> List<T>:")
expect(src).to_contain("while i >= 0:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Utils

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
