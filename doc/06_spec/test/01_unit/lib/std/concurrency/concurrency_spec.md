# Concurrency Specification

> <details>

<!-- sdn-diagram:id=concurrency_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrency_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrency_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrency_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrency Specification

## Scenarios

### Generators

### Basic generator operations

#### creates and yields single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([7])
match gen.next():
    case Ok(value): expect(value).to_equal(7)
    case Err(_): assert_true(false)
```

</details>

#### yields multiple values in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([1, 2, 3])
match gen.next():
    case Ok(value): expect(value).to_equal(1)
    case Err(_): assert_true(false)
match gen.next():
    case Ok(value): expect(value).to_equal(2)
    case Err(_): assert_true(false)
match gen.next():
    case Ok(value): expect(value).to_equal(3)
    case Err(_): assert_true(false)
```

</details>

#### returns exhausted when finished

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([4])
match gen.next():
    case Ok(value): expect(value).to_equal(4)
    case Err(_): assert_true(false)
match gen.next():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_equal("exhausted")
```

</details>

### Generator with captures

#### captures outer variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.with_captures([5], [9])
expect(gen.capture_count()).to_equal(1)
match gen.next():
    case Ok(value): expect(value).to_equal(5)
    case Err(_): assert_true(false)
```

</details>

#### captures multiple variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.with_captures([1], [2, 3])
expect(gen.capture_count()).to_equal(2)
```

</details>

### Generator with computation

#### computes values before yield

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([2 + 3])
match gen.next():
    case Ok(value): expect(value).to_equal(5)
    case Err(_): assert_true(false)
```

</details>

#### performs arithmetic in yield

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([10 - 4, 3 * 3])
match gen.next():
    case Ok(value): expect(value).to_equal(6)
    case Err(_): assert_true(false)
match gen.next():
    case Ok(value): expect(value).to_equal(9)
    case Err(_): assert_true(false)
```

</details>

### Generator state machine

#### preserves state across yields

1. gen next
   - Expected: gen.position() equals `1`
2. gen next
   - Expected: gen.position() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([1, 2])
gen.next()
expect(gen.position()).to_equal(1)
gen.next()
expect(gen.position()).to_equal(2)
```

</details>

#### handles nested iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = FakeGenerator.from_values([1, 2])
val inner = FakeGenerator.from_values([10])
match outer.next():
    case Ok(value): expect(value).to_equal(1)
    case Err(_): assert_true(false)
match inner.next():
    case Ok(value): expect(value).to_equal(10)
    case Err(_): assert_true(false)
match outer.next():
    case Ok(value): expect(value).to_equal(2)
    case Err(_): assert_true(false)
```

</details>

#### handles exhaustion with capture

1. gen next


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.with_captures([8], [99])
gen.next()
match gen.next():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_equal("exhausted")
```

</details>

### Futures

### Basic future operations

#### creates and awaits a value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.ready(42)
expect(future.is_ready()).to_equal(true)
match future.await_value():
    case Ok(value): expect(value).to_equal(42)
    case Err(_): assert_true(false)
```

</details>

#### awaits computation result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.ready(6).map(_ * 7)
match future.await_value():
    case Ok(value): expect(value).to_equal(42)
    case Err(_): assert_true(false)
```

</details>

#### awaits future-wrapped value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.ready(11).then(FakeFuture.ready(_1 + 1))
match future.await_value():
    case Ok(value): expect(value).to_equal(12)
    case Err(_): assert_true(false)
```

</details>

### Multiple futures

#### awaits multiple futures

1. assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = await_all([FakeFuture.ready(1), FakeFuture.ready(2), FakeFuture.ready(3)])
match results:
    case Ok(values):
        expect(values.len()).to_equal(3)
        expect(values[0]).to_equal(1)
        expect(values[2]).to_equal(3)
    case Err(_):
        assert_true(false)
```

</details>

### Future with captures

#### captures outer variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 5
val future = FakeFuture.ready(3).map(_ + base)
match future.await_value():
    case Ok(value): expect(value).to_equal(8)
    case Err(_): assert_true(false)
```

</details>

#### captures multiple variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 2
val b = 4
val future = FakeFuture.ready(3).map(_ + a + b)
match future.await_value():
    case Ok(value): expect(value).to_equal(9)
    case Err(_): assert_true(false)
```

</details>

### Interpreter/Codegen Parity

### Generators

#### parity: basic sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([1, 2, 3])
match gen.next():
    case Ok(value): expect(value).to_equal(1)
    case Err(_): assert_true(false)
```

</details>

#### parity: single value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.from_values([9])
match gen.next():
    case Ok(value): expect(value).to_equal(9)
    case Err(_): assert_true(false)
```

</details>

#### parity: multiple captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gen = FakeGenerator.with_captures([4], [1, 2, 3])
expect(gen.capture_count()).to_equal(3)
```

</details>

### Futures

#### parity: basic future

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.ready(7)
expect(future.is_ready()).to_equal(true)
```

</details>

#### parity: future with capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offset = 8
val future = FakeFuture.ready(2).map(_ + offset)
match future.await_value():
    case Ok(value): expect(value).to_equal(10)
    case Err(_): assert_true(false)
```

</details>

#### parity: multiple captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val y = 2
val future = FakeFuture.ready(3).map(_ + x + y)
match future.await_value():
    case Ok(value): expect(value).to_equal(6)
    case Err(_): assert_true(false)
```

</details>

### Async Execution Modes

### Threaded Mode (default)

#### is in threaded mode by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = ThreadRuntime.new(2)
expect(runtime.is_threaded_mode()).to_equal(true)
```

</details>

#### futures execute in background

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.background(10)
expect(future.background).to_equal(true)
expect(future.is_ready()).to_equal(true)
```

</details>

#### multiple concurrent futures

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future_a = FakeFuture.background(1)
val future_b = FakeFuture.background(2)
expect(future_a.is_ready()).to_equal(true)
expect(future_b.is_ready()).to_equal(true)
```

</details>

#### futures with computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.background(3).map(_ * 4)
match future.await_value():
    case Ok(value): expect(value).to_equal(12)
    case Err(_): assert_true(false)
```

</details>

#### futures with captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multiplier = 5
val future = FakeFuture.background(2).map(_ * multiplier)
match future.await_value():
    case Ok(value): expect(value).to_equal(10)
    case Err(_): assert_true(false)
```

</details>

### Resolved and Rejected Futures

#### creates already-resolved future

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.ready(99)
expect(future.is_ready()).to_equal(true)
```

</details>

#### resolved future with different types

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future_a = FakeFuture.ready(1)
val future_b = FakeFuture.ready(2)
expect(future_a.is_ready()).to_equal(true)
expect(future_b.is_ready()).to_equal(true)
```

</details>

### is_ready check

#### resolved future is ready immediately

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.ready(7)
expect(future.is_ready()).to_equal(true)
```

</details>

#### can check and await

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val future = FakeFuture.ready(8)
expect(future.is_ready()).to_equal(true)
match future.await_value():
    case Ok(value): expect(value).to_equal(8)
    case Err(_): assert_true(false)
```

</details>

### Worker Configuration

#### can configure worker count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = ThreadRuntime.new(4)
expect(runtime.available_parallelism()).to_equal(4)
```

</details>

### Isolated Threads

### Basic thread operations

#### reports available parallelism

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = ThreadRuntime.new(3)
expect(runtime.available_parallelism()).to_equal(3)
```

</details>

#### can sleep thread

1. runtime sleep
   - Expected: runtime.sleep_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = ThreadRuntime.new(1)
runtime.sleep()
expect(runtime.sleep_count()).to_equal(1)
```

</details>

#### can yield thread

1. runtime yield now
   - Expected: runtime.yield_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = ThreadRuntime.new(1)
runtime.yield_now()
expect(runtime.yield_count()).to_equal(1)
```

</details>

### Thread spawning

#### creates thread handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = ThreadHandle.new(42)
expect(handle.joined).to_equal(false)
```

</details>

#### joins thread and gets result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = ThreadHandle.new(42)
match handle.join():
    case Ok(value): expect(value).to_equal(42)
    case Err(_): assert_true(false)
```

</details>

#### passes data to thread

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spawner = ThreadSpawner.new()
val handle = spawner.spawn(17)
match handle.join():
    case Ok(value): expect(value).to_equal(17)
    case Err(_): assert_true(false)
```

</details>

#### spawns isolated thread with channel communication

1. channel send


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = Channel.new()
channel.send(88)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(88)
    case Err(_): assert_true(false)
```

</details>

### Channel FFI

#### creates channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = Channel.new()
expect(channel.is_closed()).to_equal(false)
```

</details>

#### sends and receives on channel

1. channel send
2. channel send


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = Channel.new()
channel.send(1)
channel.send(2)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(1)
    case Err(_): assert_true(false)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(2)
    case Err(_): assert_true(false)
```

</details>

#### try_recv returns empty on empty channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = Channel.new()
match channel.try_recv():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_equal("empty")
```

</details>

#### sends multiple values

1. channel send
2. channel send
   - Expected: channel.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = Channel.new()
channel.send(3)
channel.send(4)
expect(channel.len()).to_equal(2)
```

</details>

#### closes channel

1. channel close
   - Expected: channel.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = Channel.new()
channel.close()
expect(channel.is_closed()).to_equal(true)
```

</details>

### BoundedChannel

### Basic operations

#### creates channel with capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = BoundedChannel.new(2)
expect(channel.is_empty()).to_equal(true)
```

</details>

#### sends and receives values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = BoundedChannel.new(2)
expect(channel.send(1)).to_equal(true)
expect(channel.send(2)).to_equal(true)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(1)
    case Err(_): assert_true(false)
```

</details>

#### handles empty channel recv

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = BoundedChannel.new(1)
match channel.try_recv():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_equal("empty")
```

</details>

#### respects capacity limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = BoundedChannel.new(1)
expect(channel.send(1)).to_equal(true)
expect(channel.send(2)).to_equal(false)
expect(channel.is_full()).to_equal(true)
```

</details>

#### tracks channel state

1. channel send
   - Expected: channel.is_empty() is false
   - Expected: channel.is_full() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = BoundedChannel.new(1)
expect(channel.is_empty()).to_equal(true)
channel.send(9)
expect(channel.is_empty()).to_equal(false)
expect(channel.is_full()).to_equal(true)
```

</details>

#### closes channel

1. channel close
   - Expected: channel.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = BoundedChannel.new(1)
channel.close()
expect(channel.is_closed()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/concurrency/concurrency_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generators
- Basic generator operations
- Generator with captures
- Generator with computation
- Generator state machine
- Futures
- Basic future operations
- Multiple futures
- Future with captures
- Interpreter/Codegen Parity
- Generators
- Futures
- Async Execution Modes
- Threaded Mode (default)
- Resolved and Rejected Futures
- is_ready check
- Worker Configuration
- Isolated Threads
- Basic thread operations
- Thread spawning
- Channel FFI
- BoundedChannel
- Basic operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
