# Request Queue Specification

> 1. enqueue

<!-- sdn-diagram:id=request_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=request_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

request_queue_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=request_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Request Queue Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/service/request_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### Request Queue - FIFO Ordering

#### dequeues in insertion order within same lane

1. enqueue
2. enqueue
3. enqueue
   - Expected: e1.payload equals `first`
   - Expected: e2.payload equals `second`
   - Expected: e3.payload equals `third`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
enqueue(q, "first", 0i64)
enqueue(q, "second", 0i64)
enqueue(q, "third", 0i64)
val e1 = dequeue(q)
val e2 = dequeue(q)
val e3 = dequeue(q)
expect(e1.payload).to_equal("first")
expect(e2.payload).to_equal("second")
expect(e3.payload).to_equal("third")
```

</details>

#### returns sentinel for empty queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
val e = dequeue(q)
expect(e.id).to_equal("")
expect(e.lane).to_equal(-1i64)
```

</details>

### Request Queue - Priority Lanes

#### drains high-priority lane before low

1. enqueue
2. enqueue
3. enqueue
   - Expected: e1.payload equals `high-1`
   - Expected: e2.payload equals `low-1`
   - Expected: e3.payload equals `low-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
enqueue(q, "low-1", 0i64)
enqueue(q, "high-1", 1i64)
enqueue(q, "low-2", 0i64)
val e1 = dequeue(q)
val e2 = dequeue(q)
val e3 = dequeue(q)
expect(e1.payload).to_equal("high-1")
expect(e2.payload).to_equal("low-1")
expect(e3.payload).to_equal("low-2")
```

</details>

#### tracks queue length correctly

1. enqueue
2. enqueue
   - Expected: queue_len(q) equals `2i64`
3. dequeue
   - Expected: queue_len(q) equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
expect(queue_len(q)).to_equal(0i64)
enqueue(q, "a", 0i64)
enqueue(q, "b", 1i64)
expect(queue_len(q)).to_equal(2i64)
dequeue(q)
expect(queue_len(q)).to_equal(1i64)
```

</details>

#### is_empty reflects state

1. enqueue
   - Expected: queue_is_empty(q) is false
2. dequeue
   - Expected: queue_is_empty(q) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
expect(queue_is_empty(q)).to_equal(true)
enqueue(q, "item", 0i64)
expect(queue_is_empty(q)).to_equal(false)
dequeue(q)
expect(queue_is_empty(q)).to_equal(true)
```

</details>

### Request Queue - Shutdown Drain

#### drain returns all entries and empties queue

1. enqueue
2. enqueue
3. enqueue
   - Expected: drained.len() equals `3i64`
   - Expected: queue_is_empty(q) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
enqueue(q, "a", 1i64)
enqueue(q, "b", 0i64)
enqueue(q, "c", 1i64)
val drained = queue_drain(q)
expect(drained.len()).to_equal(3i64)
expect(queue_is_empty(q)).to_equal(true)
```

</details>

#### drain on empty queue returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
val drained = queue_drain(q)
expect(drained.len()).to_equal(0i64)
```

</details>

#### assigns unique IDs to entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = request_queue_new()
val id1 = enqueue(q, "a", 0i64)
val id2 = enqueue(q, "b", 0i64)
expect(id1).to_not_equal(id2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
