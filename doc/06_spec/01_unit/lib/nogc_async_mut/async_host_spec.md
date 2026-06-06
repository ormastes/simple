# Async Host Specification

> <details>

<!-- sdn-diagram:id=async_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_host_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Host Specification

## Scenarios

### Async Host Runtime

#### should define host future states and completion APIs

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = async_host_source("future.spl")
expect(src.contains("class HostFuture<T>")).to_equal(true)
expect(src.contains("enum FutureState<T>")).to_equal(true)
expect(src.contains("static fn ready(value: T)")).to_equal(true)
expect(src.contains("static fn pending()")).to_equal(true)
expect(src.contains("static fn failed(err: AsyncError)")).to_equal(true)
expect(src.contains("me complete(value: T)")).to_equal(true)
expect(src.contains("me fail(err: AsyncError)")).to_equal(true)
```

</details>

#### should define promise pair completion and failure APIs

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = async_host_source("promise.spl")
expect(src.contains("class HostPromise<T>")).to_equal(true)
expect(src.contains("static fn new() -> (HostFuture<T>, HostPromise<T>)")).to_equal(true)
expect(src.contains("me complete(value: T) -> bool")).to_equal(true)
expect(src.contains("me fail(err: AsyncError) -> bool")).to_equal(true)
expect(src.contains("fn is_completed() -> bool")).to_equal(true)
```

</details>

#### should define task handle join cancellation and state APIs

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = async_host_source("handle.spl")
expect(src.contains("class HostTaskHandle<T>")).to_equal(true)
expect(src.contains("fn try_join() -> Option<T>")).to_equal(true)
expect(src.contains("fn try_join_result() -> Option<Result<T, AsyncError>>")).to_equal(true)
expect(src.contains("fn join() -> HostFuture<T>")).to_equal(true)
expect(src.contains("me cancel()")).to_equal(true)
expect(src.contains("fn is_cancelled() -> bool")).to_equal(true)
```

</details>

#### should define dynamic join set and unordered future collections

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val join_src = async_host_source("joinset.spl")
val unordered_src = async_host_source("unordered.spl")
expect(join_src.contains("class HostJoinSet<T>")).to_equal(true)
expect(join_src.contains("me add_task(f: fn() -> T) -> usize")).to_equal(true)
expect(join_src.contains("fn try_join_next() -> Option<(usize, T)>")).to_equal(true)
expect(join_src.contains("me cancel_all()")).to_equal(true)
expect(unordered_src.contains("class HostFuturesUnordered<T>")).to_equal(true)
expect(unordered_src.contains("fn poll_next(cx: Context) -> Poll<Option<T>>")).to_equal(true)
```

</details>

#### should define scheduler modes and work stealing queues

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = async_host_source("scheduler.spl")
expect(src.contains("struct WorkStealingQueue")).to_equal(true)
expect(src.contains("enum SchedulerMode")).to_equal(true)
expect(src.contains("class HostScheduler")).to_equal(true)
expect(src.contains("static fn new(worker_count: usize)")).to_equal(true)
expect(src.contains("static fn new_multi_threaded(worker_count: usize)")).to_equal(true)
expect(src.contains("me schedule(priority: Priority")).to_equal(true)
expect(src.contains("fn wake_task(task_id: usize)")).to_equal(true)
```

</details>

#### should wire multi threaded runtime through thread safe queues

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime_src = async_host_source("runtime.spl")
val scheduler_src = async_host_source("scheduler.spl")
expect(runtime_src.contains("enum RuntimeMode")).to_equal(true)
expect(runtime_src.contains("static fn multi_threaded(num_threads: usize)")).to_equal(true)
expect(runtime_src.contains("HostScheduler.new_multi_threaded(num_threads)")).to_equal(true)
expect(runtime_src.contains("fn is_multi_threaded() -> bool")).to_equal(true)
expect(scheduler_src.contains("thread_safe_queues: [ThreadSafeQueue]")).to_equal(true)
expect(scheduler_src.contains("thread_queues = thread_queues.push(ThreadSafeQueue.new())")).to_equal(true)
```

</details>

#### should expose waker context and combinator surfaces

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val waker_src = async_host_source("waker.spl")
val combinator_src = async_host_source("combinators.spl")
expect(waker_src.contains("static fn new(task_id: usize, scheduler_ref: usize)")).to_equal(true)
expect(waker_src.contains("me wake()")).to_equal(true)
expect(waker_src.contains("me wake_by_ref()")).to_equal(true)
expect(waker_src.contains("fn will_wake(other: Waker) -> bool")).to_equal(true)
expect(combinator_src.contains("fn join_all<T>")).to_equal(true)
expect(combinator_src.contains("fn select<T>")).to_equal(true)
expect(combinator_src.contains("fn race<T>")).to_equal(true)
expect(combinator_src.contains("fn timeout<T>")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_host_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Async Host Runtime

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
