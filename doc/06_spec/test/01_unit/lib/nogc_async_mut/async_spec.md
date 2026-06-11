# Async Specification

> <details>

<!-- sdn-diagram:id=async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Specification

## Scenarios

### Async functions

#### Poll.Ready creates ready result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Poll__Ready(42)
expect(p.is_ready()).to_equal(true)
expect(p.is_pending()).to_equal(false)
```

</details>

#### Poll.unwrap extracts value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Poll__Ready(42)
expect(p.unwrap()).to_equal(42)
```

</details>

#### AsyncError has messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(AsyncError.Timeout.message()).to_equal("operation timed out")
expect(AsyncError.Cancelled.message()).to_equal("operation cancelled")
expect(AsyncError.CapacityExceeded.message()).to_equal("capacity exceeded")
```

</details>

### Futures

#### TaskState lifecycle

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TaskState.Pending.is_runnable()).to_equal(true)
expect(TaskState.Suspended.is_runnable()).to_equal(true)
expect(TaskState.Running.is_runnable()).to_equal(false)
expect(TaskState.Completed.is_terminal()).to_equal(true)
expect(TaskState.Cancelled.is_terminal()).to_equal(true)
expect(TaskState.Failed.is_terminal()).to_equal(true)
expect(TaskState.Pending.is_terminal()).to_equal(false)
```

</details>

#### Priority ordering

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Priority.Critical.to_i32()).to_equal(0)
expect(Priority.High.to_i32()).to_equal(1)
expect(Priority.Normal.to_i32()).to_equal(2)
expect(Priority.Low.to_i32()).to_equal(3)
expect(Priority.Idle.to_i32()).to_equal(4)
expect(Priority.High.to_i32()).to_be_less_than(Priority.Low.to_i32())
```

</details>

#### CancellationToken works

1. var token = CancellationToken new
   - Expected: token.is_cancelled() is false
2. token cancel
   - Expected: token.is_cancelled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var token = CancellationToken.new()
expect(token.is_cancelled()).to_equal(false)
token.cancel()
expect(token.is_cancelled()).to_equal(true)
match token.check():
    case Err(msg): expect(msg).to_equal("cancelled")
    case Ok(_): expect(true).to_equal(false)
```

</details>

### Concurrent execution

#### runs tasks concurrently

1. var scheduler = HostScheduler new
2. scheduler schedule
3. scheduler schedule
4. scheduler run
   - Expected: scheduler.is_idle() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = HostScheduler.new(1)
scheduler.schedule(Priority.Normal, \: Poll__Ready(()))
scheduler.schedule(Priority.Normal, \: Poll__Ready(()))
scheduler.run()
expect(scheduler.is_idle()).to_equal(true)
```

</details>

#### selects first completed future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures = [HostFuture.ready(42), HostFuture.pending()]
val result = select(futures)
expect(result.is_ready()).to_equal(true)
```

</details>

### Async iterators

#### iterates over async streams

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures = [HostFuture.pending(), HostFuture.ready(42)]
val result = select(futures)
expect(result.is_ready()).to_equal(true)
```

</details>

### Timeouts

#### times out slow operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = timeout(HostFuture.ready(42), 1000)
expect(result.is_ready()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Async functions
- Futures
- Concurrent execution
- Async iterators
- Timeouts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
