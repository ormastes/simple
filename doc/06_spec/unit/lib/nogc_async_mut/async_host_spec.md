# Async Host Specification

> Tests covering Async Host Runtime.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Host Specification

## Scenarios

### Async Host Runtime

#### should define host future states and completion APIs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should define host future states and completion APIs
   - Expected: src contains `class HostFuture<T>`
   - Expected: src contains `enum FutureState<T>`
   - Expected: src contains `static fn ready(value: T)`
   - Expected: src contains `static fn pending()`
   - Expected: src contains `static fn failed(err: AsyncError)`
   - Expected: src contains `me complete(value: T)`
   - Expected: src contains `me fail(err: AsyncError)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should define host future states and completion APIs")
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

- should define promise pair completion and failure APIs
   - Expected: src contains `class HostPromise<T>`
   - Expected: src contains `static fn new() -> (HostFuture<T>, HostPromise<T>)`
   - Expected: src contains `me complete(value: T) -> bool`
   - Expected: src contains `me fail(err: AsyncError) -> bool`
   - Expected: src contains `fn is_completed() -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should define promise pair completion and failure APIs")
val src = async_host_source("promise.spl")
expect(src.contains("class HostPromise<T>")).to_equal(true)
expect(src.contains("static fn new() -> (HostFuture<T>, HostPromise<T>)")).to_equal(true)
expect(src.contains("me complete(value: T) -> bool")).to_equal(true)
expect(src.contains("me fail(err: AsyncError) -> bool")).to_equal(true)
expect(src.contains("fn is_completed() -> bool")).to_equal(true)
```

</details>

#### should define task handle join cancellation and state APIs

- should define task handle join cancellation and state APIs
   - Expected: src contains `class HostTaskHandle<T>`
   - Expected: src contains `fn try_join() -> Option<T>`
   - Expected: src contains `fn try_join_result() -> Option<Result<T, AsyncError>>`
   - Expected: src contains `fn join() -> HostFuture<T>`
   - Expected: src contains `me cancel()`
   - Expected: src contains `fn is_cancelled() -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should define task handle join cancellation and state APIs")
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

- should define dynamic join set and unordered future collections
   - Expected: join_src contains `class HostJoinSet<T>`
   - Expected: join_src contains `completed_head: usize`
   - Expected: join_src contains `me add_task(f: fn() -> T) -> usize`
   - Expected: join_src contains `fn try_join_next() -> Option<(usize, T)>`
   - Expected: join_src does not contain `self.completed_queue = self.completed_queue[1:]`
   - Expected: join_src contains `self.completed_queue = self.completed_queue[self.completed_head:]`
   - Expected: join_src contains `me cancel_all()`
   - Expected: unordered_src contains `class HostFuturesUnordered<T>`
   - Expected: unordered_src contains `fn poll_next(cx: Context) -> Poll<Option<T>>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should define dynamic join set and unordered future collections")
val join_src = async_host_source("joinset.spl")
val unordered_src = async_host_source("unordered.spl")
expect(join_src.contains("class HostJoinSet<T>")).to_equal(true)
expect(join_src.contains("completed_head: usize")).to_equal(true)
expect(join_src.contains("me add_task(f: fn() -> T) -> usize")).to_equal(true)
expect(join_src.contains("fn try_join_next() -> Option<(usize, T)>")).to_equal(true)
expect(join_src.contains("self.completed_queue = self.completed_queue[1:]")).to_equal(false)
expect(join_src.contains("self.completed_queue = self.completed_queue[self.completed_head:]")).to_equal(true)
expect(join_src.contains("me cancel_all()")).to_equal(true)
expect(unordered_src.contains("class HostFuturesUnordered<T>")).to_equal(true)
expect(unordered_src.contains("fn poll_next(cx: Context) -> Poll<Option<T>>")).to_equal(true)
```

</details>

#### should define scheduler modes and work stealing queues

- should define scheduler modes and work stealing queues
   - Expected: src contains `struct WorkStealingQueue`
   - Expected: src contains `enum SchedulerMode`
   - Expected: src contains `class HostScheduler`
   - Expected: src contains `global_head: usize`
   - Expected: src contains `static fn new(worker_count: usize)`
   - Expected: src contains `static fn new_multi_threaded(worker_count: usize)`
   - Expected: src contains `me schedule(priority: Priority`
   - Expected: src contains `fn wake_task(task_id: usize)`
   - Expected: src does not contain `self.global_queue = self.global_queue[1:]`
   - Expected: src contains `self.global_queue = self.global_queue[self.global_head:]`
   - Expected: src does not contain `self.global_head * 2`
   - Expected: src contains `self.global_queue.len() - self.global_head`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should define scheduler modes and work stealing queues")
val src = async_host_source("scheduler.spl")
expect(src.contains("struct WorkStealingQueue")).to_equal(true)
expect(src.contains("enum SchedulerMode")).to_equal(true)
expect(src.contains("class HostScheduler")).to_equal(true)
expect(src.contains("global_head: usize")).to_equal(true)
expect(src.contains("static fn new(worker_count: usize)")).to_equal(true)
expect(src.contains("static fn new_multi_threaded(worker_count: usize)")).to_equal(true)
expect(src.contains("me schedule(priority: Priority")).to_equal(true)
expect(src.contains("fn wake_task(task_id: usize)")).to_equal(true)
expect(src.contains("self.global_queue = self.global_queue[1:]")).to_equal(false)
expect(src.contains("self.global_queue = self.global_queue[self.global_head:]")).to_equal(true)
expect(src.contains("self.global_head * 2")).to_equal(false)
expect(src.contains("self.global_queue.len() - self.global_head")).to_equal(true)
```

</details>

#### should wire multi threaded runtime through thread safe queues

- should wire multi threaded runtime through thread safe queues
   - Expected: runtime_src contains `enum RuntimeMode`
   - Expected: runtime_src contains `static fn multi_threaded(num_threads: usize)`
   - Expected: runtime_src contains `HostScheduler.new_multi_threaded(`
   - Expected: runtime_src contains `fn is_multi_threaded() -> bool`
   - Expected: scheduler_src contains `thread_safe_queues:`
   - Expected: scheduler_src contains `ThreadSafeQueue.new()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should wire multi threaded runtime through thread safe queues")
val runtime_src = async_host_source("runtime.spl")
val scheduler_src = async_host_source("scheduler.spl")
expect(runtime_src.contains("enum RuntimeMode")).to_equal(true)
expect(runtime_src.contains("static fn multi_threaded(num_threads: usize)")).to_equal(true)
expect(runtime_src.contains("HostScheduler.new_multi_threaded(")).to_equal(true)
expect(runtime_src.contains("fn is_multi_threaded() -> bool")).to_equal(true)
expect(scheduler_src.contains("thread_safe_queues:")).to_equal(true)
expect(scheduler_src.contains("ThreadSafeQueue.new()")).to_equal(true)
```

</details>

#### should expose waker context and combinator surfaces

- should expose waker context and combinator surfaces
   - Expected: waker_src contains `static fn new(task_id: usize, scheduler_ref: usize)`
   - Expected: waker_src contains `me wake()`
   - Expected: waker_src contains `me wake_by_ref()`
   - Expected: waker_src contains `fn will_wake(other: Waker) -> bool`
   - Expected: combinator_src contains `fn join_all<T>`
   - Expected: combinator_src contains `fn select<T>`
   - Expected: combinator_src contains `fn race<T>`
   - Expected: combinator_src contains `fn timeout<T>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should expose waker context and combinator surfaces")
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
| Source | `test/unit/lib/nogc_async_mut/async_host_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Async Host Runtime.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4199837d7713d0186872288580122f97f211019afc32ac20efab70cba58ea5ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4199837d7713d0186872288580122f97f211019afc32ac20efab70cba58ea5ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4199837d7713d0186872288580122f97f211019afc32ac20efab70cba58ea5ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/async_host_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/async_host_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/async_host_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/async_host_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/async_host_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define host future states and completion APIs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/nogc_async_mut/async_host_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define host future states and completion APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/async_host_spec.spl:26:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define promise pair completion and failure APIs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/nogc_async_mut/async_host_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define promise pair completion and failure APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/async_host_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define task handle join cancellation and state APIs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/nogc_async_mut/async_host_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define task handle join cancellation and state APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/async_host_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define dynamic join set and unordered future collections' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/nogc_async_mut/async_host_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define scheduler modes and work stealing queues' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/lib/nogc_async_mut/async_host_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should wire multi threaded runtime through thread safe queues' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
