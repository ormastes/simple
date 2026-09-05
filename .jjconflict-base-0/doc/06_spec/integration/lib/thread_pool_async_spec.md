# thread_pool_async_spec

> Purpose: This spec proves Thread Pool Basic Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# thread_pool_async_spec

Purpose: This spec proves Thread Pool Basic Integration.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/thread_pool_async_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Thread Pool Basic Integration.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Thread Pool Basic Integration

#### when observing queue-facing thread pool behavior

#### constructs a pool with the requested worker count

- constructs a pool with the requested worker count
   - Expected: pool.num_workers equals `2`
   - Expected: pool.pending_tasks() equals `0`
   - Expected: pool.is_idle() is true
   - Expected: pool.is_shutdown() is false
   - Expected: has_callback_task_id(42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-THREADPOOLASYNC-001
step("constructs a pool with the requested worker count")
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

- uses a non-zero worker count in the default pool
- uses a non-zero worker count in the default pool
   - Expected: pool.num_workers > 0 is true
   - Expected: pool.pending_tasks() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses a non-zero worker count in the default pool")
step("uses a non-zero worker count in the default pool")
val pool = TestThreadPool.default()
expect(pool.num_workers > 0).to_equal(true)
expect(pool.pending_tasks()).to_equal(0)
```

</details>

#### tracks submitted tasks in the pending queue

- tracks submitted tasks in the pending queue
- tracks submitted tasks in the pending queue
   - Expected: pool.pending_tasks() equals `1`
   - Expected: pool.is_idle() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks submitted tasks in the pending queue")
step("tracks submitted tasks in the pending queue")
var pool = TestThreadPool.new(1)
pool.submit(11)
expect(pool.pending_tasks()).to_equal(1)
expect(pool.is_idle()).to_equal(false)
pool.shutdown_now()
```

</details>

#### queues batch submissions in order

- queues batch submissions in order
- queues batch submissions in order
   - Expected: pool.pending_tasks() equals `3`
   - Expected: pool.task_queue[0] equals `3`
   - Expected: pool.task_queue[1] equals `5`
   - Expected: pool.task_queue[2] equals `8`
   - Expected: pool.pending_tasks() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("queues batch submissions in order")
step("queues batch submissions in order")
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

- clears pending work and rejects new submissions after shutdown
- clears pending work and rejects new submissions after shutdown
   - Expected: pool.is_shutdown() is true
   - Expected: pool.pending_tasks() equals `0`
   - Expected: pool.is_idle() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clears pending work and rejects new submissions after shutdown")
step("clears pending work and rejects new submissions after shutdown")
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

- waits successfully when the pool is already idle
- waits successfully when the pool is already idle
   - Expected: pool.wait_until_idle(10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("waits successfully when the pool is already idle")
step("waits successfully when the pool is already idle")
var pool = TestThreadPool.new(1)
expect(pool.wait_until_idle(10)).to_equal(true)
pool.shutdown_now()
```

</details>

### Thread Pool with Async Runtime

#### when composing host runtime and futures

#### creates a single-threaded runtime by default

- creates a single-threaded runtime by default
- creates a single-threaded runtime by default
   - Expected: runtime.is_multi_threaded() is false
   - Expected: runtime.num_threads equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates a single-threaded runtime by default")
step("creates a single-threaded runtime by default")
val runtime = HostRuntime.new()
expect(runtime.is_multi_threaded()).to_equal(false)
expect(runtime.num_threads).to_equal(1)
```

</details>

#### keeps single-threaded mode when configured with extra work queues

- keeps single-threaded mode when configured with extra work queues
- keeps single-threaded mode when configured with extra work queues
   - Expected: runtime.is_multi_threaded() is false
   - Expected: runtime.num_threads equals `1`
   - Expected: runtime.scheduler.worker_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps single-threaded mode when configured with extra work queues")
step("keeps single-threaded mode when configured with extra work queues")
val runtime = HostRuntime.with_workers(3)
expect(runtime.is_multi_threaded()).to_equal(false)
expect(runtime.num_threads).to_equal(1)
expect(runtime.scheduler.worker_count).to_equal(3)
```

</details>

#### creates a multi-threaded runtime when explicitly requested

- creates a multi-threaded runtime when explicitly requested
- creates a multi-threaded runtime when explicitly requested
   - Expected: runtime.is_multi_threaded() is true
   - Expected: runtime.num_threads equals `2`
   - Expected: runtime.scheduler.worker_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates a multi-threaded runtime when explicitly requested")
step("creates a multi-threaded runtime when explicitly requested")
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

- blocks on an already-ready future
- blocks on an already-ready future
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("blocks on an already-ready future")
step("blocks on an already-ready future")
val result = block_on_ready(HostFuture.ready(42))
expect(result).to_equal(42)
```

</details>

#### maps ready futures before blocking on them

- maps ready futures before blocking on them
- maps ready futures before blocking on them
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps ready futures before blocking on them")
step("maps ready futures before blocking on them")
val result = block_on_ready(HostFuture.ready(7).map(_1 * 6))
expect(result).to_equal(42)
```

</details>

#### chains ready futures with then

- chains ready futures with then
- chains ready futures with then
   - Expected: result equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("chains ready futures with then")
step("chains ready futures with then")
val future = HostFuture.ready(5).then(HostFuture.ready(_1 + 8))
val result = block_on_ready(future)
expect(result).to_equal(13)
```

</details>

#### preserves pending state through map without fabricating completion

- preserves pending state through map without fabricating completion
- preserves pending state through map without fabricating completion
   - Expected: mapped.is_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves pending state through map without fabricating completion")
step("preserves pending state through map without fabricating completion")
val future = HostFuture.pending()
val mapped = future.map(_1 + 1)
expect(mapped.is_ready()).to_equal(false)
```

</details>

### Work Stealing and Load Balancing

#### when observing local versus steal-end queue semantics

#### pops from the local end in LIFO order

- pops from the local end in LIFO order
- pops from the local end in LIFO order
   - Expected: queue.pop() equals `3`
   - Expected: queue.pop() equals `2`
   - Expected: queue.pop() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pops from the local end in LIFO order")
step("pops from the local end in LIFO order")
var queue = WorkStealingQueue.new()
queue.push(1)
queue.push(2)
queue.push(3)
expect(queue.pop()).to_equal(3)
expect(queue.pop()).to_equal(2)
expect(queue.pop()).to_equal(1)
```

</details>

#### steals from the opposite end in FIFO order

- steals from the opposite end in FIFO order
- steals from the opposite end in FIFO order
   - Expected: queue.steal() equals `1`
   - Expected: queue.steal() equals `2`
   - Expected: queue.steal() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("steals from the opposite end in FIFO order")
step("steals from the opposite end in FIFO order")
var queue = WorkStealingQueue.new()
queue.push(1)
queue.push(2)
queue.push(3)
expect(queue.steal()).to_equal(1)
expect(queue.steal()).to_equal(2)
expect(queue.steal()).to_equal(3)
```

</details>

#### updates remaining length after mixed pop and steal operations

- updates remaining length after mixed pop and steal operations
- updates remaining length after mixed pop and steal operations
   - Expected: queue.len() equals `4`
   - Expected: queue.steal() equals `10`
   - Expected: queue.pop() equals `40`
   - Expected: queue.len() equals `2`
   - Expected: queue.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("updates remaining length after mixed pop and steal operations")
step("updates remaining length after mixed pop and steal operations")
var queue = WorkStealingQueue.new()
queue.push(10)
queue.push(20)
queue.push(30)
queue.push(40)
expect(queue.len()).to_equal(4)
expect(queue.steal()).to_equal(10)
expect(queue.pop()).to_equal(40)
expect(queue.len()).to_equal(2)
expect(queue.is_empty()).to_equal(false)
```

</details>

#### reports empty once all work is drained

- reports empty once all work is drained
- reports empty once all work is drained
   - Expected: queue.is_empty() is false
   - Expected: queue.pop() equals `99`
   - Expected: queue.is_empty() is true
   - Expected: queue.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports empty once all work is drained")
step("reports empty once all work is drained")
var queue = WorkStealingQueue.new()
queue.push(99)
expect(queue.is_empty()).to_equal(false)
expect(queue.pop()).to_equal(99)
expect(queue.is_empty()).to_equal(true)
expect(queue.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-THREADPOOLASYNC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `902ec15a1b74b64a6f0fba7ec882bce5f43c6bf8ad025167d6222fdaaac0b9f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `902ec15a1b74b64a6f0fba7ec882bce5f43c6bf8ad025167d6222fdaaac0b9f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `902ec15a1b74b64a6f0fba7ec882bce5f43c6bf8ad025167d6222fdaaac0b9f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/lib/thread_pool_async_spec.spl
mirror: doc/06_spec/integration/lib/thread_pool_async_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/lib/thread_pool_async_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/thread_pool_async_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/thread_pool_async_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 30 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/lib/thread_pool_async_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs a pool with the requested worker count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/thread_pool_async_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses a non-zero worker count in the default pool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/thread_pool_async_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks submitted tasks in the pending queue' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
