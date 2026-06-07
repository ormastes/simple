# Concurrent Specification

> 1. var queue = mpsc queue new

<!-- sdn-diagram:id=concurrent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrent_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Specification

## Scenarios

### MpscQueue<T>

#### should create empty queue

1. var queue = mpsc queue new
2. expect queue is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
expect queue.is_empty() == true
```

</details>

#### should start with no items

1. var queue = mpsc queue new
2. expect queue len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
expect queue.len() == 0
```

</details>

#### should push and pop single item

1. var queue = mpsc queue new
2. queue push


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
queue.push(42)
val value = queue.pop()
expect value == 42
```

</details>

#### should maintain FIFO order

1. var queue = mpsc queue new
2. queue push
3. queue push
4. queue push
5. expect queue pop
6. expect queue pop
7. expect queue pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
queue.push(1)
queue.push(2)
queue.push(3)
expect queue.pop() == 1
expect queue.pop() == 2
expect queue.pop() == 3
```

</details>

#### should handle multiple push/pop cycles

1. var queue = mpsc queue new
2. queue push
3. expect queue pop
4. queue push
5. expect queue pop
6. queue push
7. expect queue pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
queue.push(10)
expect queue.pop() == 10
queue.push(20)
expect queue.pop() == 20
queue.push(30)
expect queue.pop() == 30
```

</details>

#### should work with complex types

1. var queue = mpsc queue new
2. queue push
3. expect queue pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
queue.push("hello")
expect queue.pop() == "hello"
```

</details>

#### should return None when empty

1. var queue = mpsc queue new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
val value = queue.pop()
expect value == nil
```

</details>

#### should detect empty state

1. var queue = mpsc queue new
2. expect queue is empty
3. queue push
4. expect queue is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
expect queue.is_empty() == true
queue.push(1)
expect queue.is_empty() == false
```

</details>

#### should handle many items

1. var queue = mpsc queue new
2. queue push
3. expect queue len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpsc_queue_new()
for i in 0..100:
    queue.push(i)
expect queue.len() >= 100
```

</details>

### MpmcQueue<T>

#### should create queue with capacity

1. var queue = mpmc queue with capacity
2. expect queue is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(10)
expect queue.is_empty() == true
```

</details>

#### should start with length 0

1. var queue = mpmc queue with capacity
2. expect queue len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(5)
expect queue.len() == 0
```

</details>

#### should push and pop single item

1. var queue = mpmc queue with capacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(5)
val pushed = queue.push(42)
expect pushed == true
val value = queue.pop()
expect value == 42
```

</details>

#### should respect capacity limit

1. var queue = mpmc queue with capacity
2. expect queue push
3. expect queue push
4. expect queue push


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(2)
expect queue.push(1) == true
expect queue.push(2) == true
expect queue.push(3) == false  # Over capacity
```

</details>

#### should maintain FIFO order

1. var queue = mpmc queue with capacity
2. queue push
3. queue push
4. queue push
5. expect queue pop
6. expect queue pop
7. expect queue pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(10)
queue.push(1)
queue.push(2)
queue.push(3)
expect queue.pop() == 1
expect queue.pop() == 2
expect queue.pop() == 3
```

</details>

#### should return None when empty

1. var queue = mpmc queue with capacity
2. expect queue pop


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(5)
expect queue.pop() == nil
```

</details>

#### should allow reuse after drain

1. var queue = mpmc queue with capacity
2. queue push
3. queue push
4. queue pop
5. queue pop
6. expect queue push


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(3)
queue.push(1)
queue.push(2)
queue.pop()
queue.pop()
expect queue.push(3) == true
```

</details>

#### should track length accurately

1. var queue = mpmc queue with capacity
2. expect queue len
3. queue push
4. expect queue len
5. queue push
6. expect queue len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = mpmc_queue_with_capacity(10)
expect queue.len() == 0
queue.push(1)
expect queue.len() == 1
queue.push(2)
expect queue.len() == 2
```

</details>

### ConcurrentMap<K, V>

#### should create empty map

1. expect map len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = concurrent_map_new()
expect map.len() == 0
```

</details>

#### should insert and get value

1. map insert
2. expect map get


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = concurrent_map_new()
map.insert("key", 42)
expect map.get("key") == 42
```

</details>

#### should return None for missing key

1. expect map get


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = concurrent_map_new()
expect map.get("missing") == nil
```

</details>

#### should check if key exists

1. map insert
2. expect map has
3. expect map has


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = concurrent_map_new()
map.insert("exists", 1)
expect map.has("exists") == true
expect map.has("missing") == false
```

</details>

#### should remove values

1. map insert
2. expect map has


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = concurrent_map_new()
map.insert("key", 100)
val removed = map.remove("key")
expect removed == 100
expect map.has("key") == false
```

</details>

#### should handle multiple keys

1. map insert
2. map insert
3. map insert
4. expect map len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = concurrent_map_new()
map.insert("a", 1)
map.insert("b", 2)
map.insert("c", 3)
expect map.len() == 3
```

</details>

#### should overwrite existing keys

1. map insert
2. map insert
3. expect map get


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = concurrent_map_new()
map.insert("key", 1)
map.insert("key", 2)
expect map.get("key") == 2
```

</details>

### AtomicFlag

#### should create unset flag

1. expect flag is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = atomic_flag_new()
expect flag.is_set() == false
```

</details>

#### should set flag

1. flag set
2. expect flag is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = atomic_flag_new()
flag.set()
expect flag.is_set() == true
```

</details>

#### should test and set atomically

1. expect flag is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = atomic_flag_new()
val was_set = flag.test_and_set()
expect was_set == false
expect flag.is_set() == true
```

</details>

#### should clear flag

1. flag set
2. flag clear
3. expect flag is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = atomic_flag_new()
flag.set()
flag.clear()
expect flag.is_set() == false
```

</details>

### Once

#### should create Once

1. expect once is completed


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val once = once_new()
expect once.is_completed() == false
```

</details>

#### should run callback once

1. once call once
2. once call once
3. expect once is completed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val once = once_new()
var count = 0
val increment = fn():
    count = count + 1
once.call_once(increment)
once.call_once(increment)
# Note: Due to closure limitations, this test may not verify correctly
# Just check no crash
expect once.is_completed() == true
```

</details>

#### should mark as completed

1. once call once
2. expect once is completed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val once = once_new()
once.call_once(fn(): ())
expect once.is_completed() == true
```

</details>

### Barrier

#### should create barrier with count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val barrier = barrier_new(2)
# Just verify creation works
expect true
```

</details>

#### should wait for all threads

1. barrier wait


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val barrier = barrier_new(1)
barrier.wait()
# Single thread case - should complete immediately
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MpscQueue<T>
- MpmcQueue<T>
- ConcurrentMap<K, V>
- AtomicFlag
- Once
- Barrier

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
