# Thread Pool Async Specification

> <details>

<!-- sdn-diagram:id=thread_pool_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_pool_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_pool_async_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_pool_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Pool Async Specification

## Scenarios

### Thread Pool Basic Integration

#### when observing queue-facing thread pool behavior

#### constructs a pool with the requested worker count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = TestThreadPool.new(2)
expect(pool.num_workers).to_equal(2)
expect(pool.pending_tasks()).to_equal(0)
expect(pool.is_idle()).to_equal(true)
expect(pool.is_shutdown()).to_equal(false)
GLOBAL_TASK_CALLBACK_IDS = [42]
expect(has_callback_task_id(42)).to_equal(true)
```

</details>

#### uses a non-zero worker count in the default pool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = TestThreadPool.default()
expect(pool.num_workers > 0).to_equal(true)
expect(pool.pending_tasks()).to_equal(0)
```

</details>

#### tracks submitted tasks in the pending queue

- var pool = TestThreadPool new
- pool submit
   - Expected: pool.pending_tasks() equals `1`
   - Expected: pool.is_idle() is false
- pool shutdown now


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = TestThreadPool.new(1)
pool.submit(11)
expect(pool.pending_tasks()).to_equal(1)
expect(pool.is_idle()).to_equal(false)
pool.shutdown_now()
```

</details>

#### queues batch submissions in order

- var pool = TestThreadPool new
- pool submit batch
   - Expected: pool.pending_tasks() equals `3`
   - Expected: pool.task_queue[0] equals `3`
   - Expected: pool.task_queue[1] equals `5`
   - Expected: pool.task_queue[2] equals `8`
- pool shutdown now
   - Expected: pool.pending_tasks() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = TestThreadPool.new(1)
pool.submit_batch([3, 5, 8])
expect(pool.pending_tasks()).to_equal(3)
expect(pool.task_queue[0]).to_equal(3)
expect(pool.task_queue[1]).to_equal(5)
expect(pool.task_queue[2]).to_equal(8)
pool.shutdown_now()
expect(pool.pending_tasks()).to_equal(0)
```

</details>

#### clears pending work and rejects new submissions after shutdown

- var pool = TestThreadPool new
- pool submit batch
- pool shutdown now
- pool submit
   - Expected: pool.is_shutdown() is true
   - Expected: pool.pending_tasks() equals `0`
   - Expected: pool.is_idle() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = TestThreadPool.new(1)
pool.submit_batch([1, 2, 3])
pool.shutdown_now()
pool.submit(99)
expect(pool.is_shutdown()).to_equal(true)
expect(pool.pending_tasks()).to_equal(0)
expect(pool.is_idle()).to_equal(true)
```

</details>

#### waits successfully when the pool is already idle

- var pool = TestThreadPool new
   - Expected: pool.wait_until_idle(10) is true
- pool shutdown now


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = TestThreadPool.new(1)
expect(pool.wait_until_idle(10)).to_equal(true)
pool.shutdown_now()
```

</details>

### Thread Pool with Async Runtime

#### when composing host runtime and futures

#### creates a single-threaded runtime by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = HostRuntime.new()
expect(runtime.is_multi_threaded()).to_equal(false)
expect(runtime.num_threads).to_equal(1)
```

</details>

#### keeps single-threaded mode when configured with extra work queues

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = HostRuntime.with_workers(3)
expect(runtime.is_multi_threaded()).to_equal(false)
expect(runtime.num_threads).to_equal(1)
expect(runtime.scheduler.worker_count).to_equal(3)
```

</details>

#### creates a multi-threaded runtime when explicitly requested

- scheduler: HostScheduler new
   - Expected: runtime.is_multi_threaded() is true
   - Expected: runtime.num_threads equals `2`
   - Expected: runtime.scheduler.worker_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = HostRuntime(
    scheduler: HostScheduler.new(2),
    next_id: 0,
    mode: RuntimeMode.MultiThreaded,
    num_threads: 2
)
expect(runtime.is_multi_threaded()).to_equal(true)
expect(runtime.num_threads).to_equal(2)
expect(runtime.scheduler.worker_count).to_equal(2)
```

</details>

#### blocks on an already-ready future

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = block_on_ready(HostFuture.ready(42))
expect(result).to_equal(42)
```

</details>

#### maps ready futures before blocking on them

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = block_on_ready(HostFuture.ready(7).map(_1 * 6))
expect(result).to_equal(42)
```

</details>

#### chains ready futures with then

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = HostFuture.ready(5).then(HostFuture.ready(_1 + 8))
val result = block_on_ready(future)
expect(result).to_equal(13)
```

</details>

#### preserves pending state through map without fabricating completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = HostFuture.pending()
val mapped = future.map(_1 + 1)
expect(mapped.is_ready()).to_equal(false)
```

</details>

### Work Stealing and Load Balancing

#### when observing local versus steal-end queue semantics

#### pops from the local end in LIFO order

- var queue = WorkStealingQueue new
- queue push
- queue push
- queue push
- expect some usize
- expect some usize
- expect some usize


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = WorkStealingQueue.new()
queue.push(1)
queue.push(2)
queue.push(3)
expect_some_usize(queue.pop(), 3)
expect_some_usize(queue.pop(), 2)
expect_some_usize(queue.pop(), 1)
```

</details>

#### steals from the opposite end in FIFO order

- var queue = WorkStealingQueue new
- queue push
- queue push
- queue push
- expect some usize
- expect some usize
- expect some usize


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = WorkStealingQueue.new()
queue.push(1)
queue.push(2)
queue.push(3)
expect_some_usize(queue.steal(), 1)
expect_some_usize(queue.steal(), 2)
expect_some_usize(queue.steal(), 3)
```

</details>

#### updates remaining length after mixed pop and steal operations

- var queue = WorkStealingQueue new
- queue push
- queue push
- queue push
- queue push
   - Expected: queue.len() equals `4`
- expect some usize
- expect some usize
   - Expected: queue.len() equals `2`
   - Expected: queue.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = WorkStealingQueue.new()
queue.push(10)
queue.push(20)
queue.push(30)
queue.push(40)
expect(queue.len()).to_equal(4)
expect_some_usize(queue.steal(), 10)
expect_some_usize(queue.pop(), 40)
expect(queue.len()).to_equal(2)
expect(queue.is_empty()).to_equal(false)
```

</details>

#### reports empty once all work is drained

- var queue = WorkStealingQueue new
- queue push
   - Expected: queue.is_empty() is false
- expect some usize
   - Expected: queue.is_empty() is true
   - Expected: queue.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = WorkStealingQueue.new()
queue.push(99)
expect(queue.is_empty()).to_equal(false)
expect_some_usize(queue.pop(), 99)
expect(queue.is_empty()).to_equal(true)
expect(queue.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/thread_pool_async_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Thread Pool Basic Integration
- Thread Pool with Async Runtime
- Work Stealing and Load Balancing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
