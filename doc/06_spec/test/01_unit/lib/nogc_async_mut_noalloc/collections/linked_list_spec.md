# Linked List Specification

> <details>

<!-- sdn-diagram:id=linked_list_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linked_list_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linked_list_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linked_list_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linked List Specification

## Scenarios

### Linked List

#### keeps pool allocated linked list node model available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = linked_list_source()

expect(source).to_contain("class ListNode:")
expect(source).to_contain("class PoolLinkedList:")
expect(source).to_contain("static fn new(capacity: i32) -> PoolLinkedList")
expect(source).to_contain("me alloc_node() -> i32")
expect(source).to_contain("me free_node(idx: i32)")
```

</details>

#### keeps linked list insertion removal and query operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = linked_list_source()

expect(source).to_contain("me push_front(value: i64) -> bool")
expect(source).to_contain("me push_back(value: i64) -> bool")
expect(source).to_contain("me pop_front() -> i64")
expect(source).to_contain("me pop_back() -> i64")
expect(source).to_contain("fn peek_front() -> i64")
expect(source).to_contain("fn peek_back() -> i64")
expect(source).to_contain("fn is_full() -> bool")
expect(source).to_contain("fn size() -> i32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linked List

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
