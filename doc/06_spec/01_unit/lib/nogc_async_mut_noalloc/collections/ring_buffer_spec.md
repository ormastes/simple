# Ring Buffer Specification

> <details>

<!-- sdn-diagram:id=ring_buffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ring_buffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ring_buffer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ring_buffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ring Buffer Specification

## Scenarios

### Ring Buffer

#### keeps circular queue operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = ring_buffer_source()

expect(source).to_contain("class RingBuffer:")
expect(source).to_contain("static fn new(capacity: i32) -> RingBuffer")
expect(source).to_contain("me enqueue(value: i64) -> bool")
expect(source).to_contain("me dequeue() -> i64")
expect(source).to_contain("fn peek() -> i64")
expect(source).to_contain("fn available() -> i32")
expect(source).to_contain("fn size() -> i32")
```

</details>

#### keeps power of two sizing and factories available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = ring_buffer_source()

expect(source).to_contain("fn next_power_of_2(n: i32) -> i32")
expect(source).to_contain("fn ring_buffer_16() -> RingBuffer")
expect(source).to_contain("fn ring_buffer_32() -> RingBuffer")
expect(source).to_contain("fn ring_buffer_64() -> RingBuffer")
expect(source).to_contain("fn ring_buffer_128() -> RingBuffer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/collections/ring_buffer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ring Buffer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
