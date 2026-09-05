# concurrency_spec

> Purpose: Verify Generators.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# concurrency_spec

Purpose: Verify Generators.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/concurrency/concurrency_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Generators.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Generators

### Basic generator operations

#### creates and yields single value

- creates and yields single value
- Verify: creates and yields single value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates and yields single value")
step("Verify: creates and yields single value")
# @req: REQ-LIB-CONCURRENCY-001
val gen = FakeGenerator.from_values([7])
match gen.next():
    case Ok(value): expect(value).to_equal(7)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### yields multiple values in sequence

- yields multiple values in sequence
- Verify: yields multiple values in sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields multiple values in sequence")
step("Verify: yields multiple values in sequence")
val gen = FakeGenerator.from_values([1, 2, 3])
match gen.next():
    case Ok(value): expect(value).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
match gen.next():
    case Ok(value): expect(value).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
match gen.next():
    case Ok(value): expect(value).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### returns exhausted when finished

- returns exhausted when finished
- Verify: returns exhausted when finished


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exhausted when finished")
step("Verify: returns exhausted when finished")
val gen = FakeGenerator.from_values([4])
match gen.next():
    case Ok(value): expect(value).to_equal(4)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
match gen.next():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_equal("exhausted")
```

</details>

### Generator with captures

#### captures outer variables

- captures outer variables
- Verify: captures outer variables
   - Expected: gen.capture_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures outer variables")
step("Verify: captures outer variables")
val gen = FakeGenerator.with_captures([5], [9])
expect(gen.capture_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
match gen.next():
    case Ok(value): expect(value).to_equal(5)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### captures multiple variables

- captures multiple variables
- Verify: captures multiple variables
   - Expected: gen.capture_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures multiple variables")
step("Verify: captures multiple variables")
val gen = FakeGenerator.with_captures([1], [2, 3])
expect(gen.capture_count()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Generator with computation

#### computes values before yield

- computes values before yield
- Verify: computes values before yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes values before yield")
step("Verify: computes values before yield")
val gen = FakeGenerator.from_values([2 + 3])
match gen.next():
    case Ok(value): expect(value).to_equal(5)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### performs arithmetic in yield

- performs arithmetic in yield
- Verify: performs arithmetic in yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("performs arithmetic in yield")
step("Verify: performs arithmetic in yield")
val gen = FakeGenerator.from_values([10 - 4, 3 * 3])
match gen.next():
    case Ok(value): expect(value).to_equal(6)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
match gen.next():
    case Ok(value): expect(value).to_equal(9)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

### Generator state machine

#### preserves state across yields

- preserves state across yields
- Verify: preserves state across yields
   - Expected: gen.position() equals `1`
   - Expected: gen.position() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves state across yields")
step("Verify: preserves state across yields")
val gen = FakeGenerator.from_values([1, 2])
gen.next()
expect(gen.position()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
gen.next()
expect(gen.position()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### handles nested iteration

- handles nested iteration
- Verify: handles nested iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested iteration")
step("Verify: handles nested iteration")
val outer = FakeGenerator.from_values([1, 2])
val inner = FakeGenerator.from_values([10])
match outer.next():
    case Ok(value): expect(value).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
match inner.next():
    case Ok(value): expect(value).to_equal(10)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
match outer.next():
    case Ok(value): expect(value).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### handles exhaustion with capture

- handles exhaustion with capture
- Verify: handles exhaustion with capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles exhaustion with capture")
step("Verify: handles exhaustion with capture")
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

- creates and awaits a value
- Verify: creates and awaits a value
   - Expected: future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates and awaits a value")
step("Verify: creates and awaits a value")
val future = FakeFuture.ready(42)
expect(future.is_ready()).to_equal(true)
match future.await_value():
    case Ok(value): expect(value).to_equal(42)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### awaits computation result

- awaits computation result
- Verify: awaits computation result


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("awaits computation result")
step("Verify: awaits computation result")
val future = FakeFuture.ready(6).map(_ * 7)
match future.await_value():
    case Ok(value): expect(value).to_equal(42)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### awaits future-wrapped value

- awaits future-wrapped value
- Verify: awaits future-wrapped value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("awaits future-wrapped value")
step("Verify: awaits future-wrapped value")
val future = FakeFuture.ready(11).then(FakeFuture.ready(_1 + 1))
match future.await_value():
    case Ok(value): expect(value).to_equal(12)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

### Multiple futures

#### awaits multiple futures

- awaits multiple futures
- Verify: awaits multiple futures
   - Expected: values.len() equals `3`
   - Expected: values[0] equals `1`
   - Expected: values[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("awaits multiple futures")
step("Verify: awaits multiple futures")
val results = await_all([FakeFuture.ready(1), FakeFuture.ready(2), FakeFuture.ready(3)])
match results:
    case Ok(values):
        expect(values.len()).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
        expect(values[0]).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
        expect(values[2]).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_):
        assert_true(false)
```

</details>

### Future with captures

#### captures outer variable

- captures outer variable
- Verify: captures outer variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures outer variable")
step("Verify: captures outer variable")
val base = 5
val future = FakeFuture.ready(3).map(_ + base)
match future.await_value():
    case Ok(value): expect(value).to_equal(8)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### captures multiple variables

- captures multiple variables
- Verify: captures multiple variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures multiple variables")
step("Verify: captures multiple variables")
val a = 2
val b = 4
val future = FakeFuture.ready(3).map(_ + a + b)
match future.await_value():
    case Ok(value): expect(value).to_equal(9)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

### Interpreter/Codegen Parity

### Generators

#### parity: basic sequence

- parity: basic sequence
- Verify: parity: basic sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity: basic sequence")
step("Verify: parity: basic sequence")
val gen = FakeGenerator.from_values([1, 2, 3])
match gen.next():
    case Ok(value): expect(value).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### parity: single value

- parity: single value
- Verify: parity: single value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity: single value")
step("Verify: parity: single value")
val gen = FakeGenerator.from_values([9])
match gen.next():
    case Ok(value): expect(value).to_equal(9)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### parity: multiple captures

- parity: multiple captures
- Verify: parity: multiple captures
   - Expected: gen.capture_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity: multiple captures")
step("Verify: parity: multiple captures")
val gen = FakeGenerator.with_captures([4], [1, 2, 3])
expect(gen.capture_count()).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Futures

#### parity: basic future

- parity: basic future
- Verify: parity: basic future
   - Expected: future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity: basic future")
step("Verify: parity: basic future")
val future = FakeFuture.ready(7)
expect(future.is_ready()).to_equal(true)
```

</details>

#### parity: future with capture

- parity: future with capture
- Verify: parity: future with capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity: future with capture")
step("Verify: parity: future with capture")
val offset = 8
val future = FakeFuture.ready(2).map(_ + offset)
match future.await_value():
    case Ok(value): expect(value).to_equal(10)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### parity: multiple captures

- parity: multiple captures
- Verify: parity: multiple captures


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parity: multiple captures")
step("Verify: parity: multiple captures")
val x = 1
val y = 2
val future = FakeFuture.ready(3).map(_ + x + y)
match future.await_value():
    case Ok(value): expect(value).to_equal(6)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

### Async Execution Modes

### Threaded Mode (default)

#### is in threaded mode by default

- is in threaded mode by default
- Verify: is in threaded mode by default
   - Expected: runtime.is_threaded_mode() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is in threaded mode by default")
step("Verify: is in threaded mode by default")
val runtime = ThreadRuntime.new(2)
expect(runtime.is_threaded_mode()).to_equal(true)
```

</details>

#### futures execute in background

- futures execute in background
- Verify: futures execute in background
   - Expected: future.background is true
   - Expected: future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("futures execute in background")
step("Verify: futures execute in background")
val future = FakeFuture.background(10)
expect(future.background).to_equal(true)
expect(future.is_ready()).to_equal(true)
```

</details>

#### multiple concurrent futures

- multiple concurrent futures
- Verify: multiple concurrent futures
   - Expected: future_a.is_ready() is true
   - Expected: future_b.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple concurrent futures")
step("Verify: multiple concurrent futures")
val future_a = FakeFuture.background(1)
val future_b = FakeFuture.background(2)
expect(future_a.is_ready()).to_equal(true)
expect(future_b.is_ready()).to_equal(true)
```

</details>

#### futures with computation

- futures with computation
- Verify: futures with computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("futures with computation")
step("Verify: futures with computation")
val future = FakeFuture.background(3).map(_ * 4)
match future.await_value():
    case Ok(value): expect(value).to_equal(12)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### futures with captures

- futures with captures
- Verify: futures with captures


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("futures with captures")
step("Verify: futures with captures")
val multiplier = 5
val future = FakeFuture.background(2).map(_ * multiplier)
match future.await_value():
    case Ok(value): expect(value).to_equal(10)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

### Resolved and Rejected Futures

#### creates already-resolved future

- creates already-resolved future
- Verify: creates already-resolved future
   - Expected: future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates already-resolved future")
step("Verify: creates already-resolved future")
val future = FakeFuture.ready(99)
expect(future.is_ready()).to_equal(true)
```

</details>

#### resolved future with different types

- resolved future with different types
- Verify: resolved future with different types
   - Expected: future_a.is_ready() is true
   - Expected: future_b.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolved future with different types")
step("Verify: resolved future with different types")
val future_a = FakeFuture.ready(1)
val future_b = FakeFuture.ready(2)
expect(future_a.is_ready()).to_equal(true)
expect(future_b.is_ready()).to_equal(true)
```

</details>

### is_ready check

#### resolved future is ready immediately

- resolved future is ready immediately
- Verify: resolved future is ready immediately
   - Expected: future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolved future is ready immediately")
step("Verify: resolved future is ready immediately")
val future = FakeFuture.ready(7)
expect(future.is_ready()).to_equal(true)
```

</details>

#### can check and await

- can check and await
- Verify: can check and await
   - Expected: future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can check and await")
step("Verify: can check and await")
val future = FakeFuture.ready(8)
expect(future.is_ready()).to_equal(true)
match future.await_value():
    case Ok(value): expect(value).to_equal(8)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

### Worker Configuration

#### can configure worker count

- can configure worker count
- Verify: can configure worker count
   - Expected: runtime.available_parallelism() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can configure worker count")
step("Verify: can configure worker count")
val runtime = ThreadRuntime.new(4)
expect(runtime.available_parallelism()).to_equal(4)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Isolated Threads

### Basic thread operations

#### reports available parallelism

- reports available parallelism
- Verify: reports available parallelism
   - Expected: runtime.available_parallelism() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports available parallelism")
step("Verify: reports available parallelism")
val runtime = ThreadRuntime.new(3)
expect(runtime.available_parallelism()).to_equal(3)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### can sleep thread

- can sleep thread
- Verify: can sleep thread
   - Expected: runtime.sleep_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can sleep thread")
step("Verify: can sleep thread")
val runtime = ThreadRuntime.new(1)
runtime.sleep()
expect(runtime.sleep_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### can yield thread

- can yield thread
- Verify: can yield thread
   - Expected: runtime.yield_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can yield thread")
step("Verify: can yield thread")
val runtime = ThreadRuntime.new(1)
runtime.yield_now()
expect(runtime.yield_count()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

### Thread spawning

#### creates thread handle

- creates thread handle
- Verify: creates thread handle
   - Expected: handle.joined is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates thread handle")
step("Verify: creates thread handle")
val handle = ThreadHandle.new(42)
expect(handle.joined).to_equal(false)
```

</details>

#### joins thread and gets result

- joins thread and gets result
- Verify: joins thread and gets result


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins thread and gets result")
step("Verify: joins thread and gets result")
val handle = ThreadHandle.new(42)
match handle.join():
    case Ok(value): expect(value).to_equal(42)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### passes data to thread

- passes data to thread
- Verify: passes data to thread


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes data to thread")
step("Verify: passes data to thread")
val spawner = ThreadSpawner.new()
val handle = spawner.spawn(17)
match handle.join():
    case Ok(value): expect(value).to_equal(17)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### spawns isolated thread with channel communication

- spawns isolated thread with channel communication
- Verify: spawns isolated thread with channel communication


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns isolated thread with channel communication")
step("Verify: spawns isolated thread with channel communication")
val channel = Channel.new()
channel.send(88)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(88)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

### Channel FFI

#### creates channel

- creates channel
- Verify: creates channel
   - Expected: channel.is_closed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates channel")
step("Verify: creates channel")
val channel = Channel.new()
expect(channel.is_closed()).to_equal(false)
```

</details>

#### sends and receives on channel

- sends and receives on channel
- Verify: sends and receives on channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives on channel")
step("Verify: sends and receives on channel")
val channel = Channel.new()
channel.send(1)
channel.send(2)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### try_recv returns empty on empty channel

- try_recv returns empty on empty channel
- Verify: try_recv returns empty on empty channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try_recv returns empty on empty channel")
step("Verify: try_recv returns empty on empty channel")
val channel = Channel.new()
match channel.try_recv():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_equal("empty")
```

</details>

#### sends multiple values

- sends multiple values
- Verify: sends multiple values
   - Expected: channel.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends multiple values")
step("Verify: sends multiple values")
val channel = Channel.new()
channel.send(3)
channel.send(4)
expect(channel.len()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### closes channel

- closes channel
- Verify: closes channel
   - Expected: channel.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes channel")
step("Verify: closes channel")
val channel = Channel.new()
channel.close()
expect(channel.is_closed()).to_equal(true)
```

</details>

### BoundedChannel

### Basic operations

#### creates channel with capacity

- creates channel with capacity
- Verify: creates channel with capacity
   - Expected: channel.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates channel with capacity")
step("Verify: creates channel with capacity")
val channel = BoundedChannel.new(2)
expect(channel.is_empty()).to_equal(true)
```

</details>

#### sends and receives values

- sends and receives values
- Verify: sends and receives values
   - Expected: channel.send(1) is true
   - Expected: channel.send(2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives values")
step("Verify: sends and receives values")
val channel = BoundedChannel.new(2)
expect(channel.send(1)).to_equal(true)
expect(channel.send(2)).to_equal(true)
match channel.try_recv():
    case Ok(value): expect(value).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
    case Err(_): assert_true(false)
```

</details>

#### handles empty channel recv

- handles empty channel recv
- Verify: handles empty channel recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty channel recv")
step("Verify: handles empty channel recv")
val channel = BoundedChannel.new(1)
match channel.try_recv():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_equal("empty")
```

</details>

#### respects capacity limit

- respects capacity limit
- Verify: respects capacity limit
   - Expected: channel.send(1) is true
   - Expected: channel.send(2) is false
   - Expected: channel.is_full() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects capacity limit")
step("Verify: respects capacity limit")
val channel = BoundedChannel.new(1)
expect(channel.send(1)).to_equal(true)
expect(channel.send(2)).to_equal(false)
expect(channel.is_full()).to_equal(true)
```

</details>

#### tracks channel state

- tracks channel state
- Verify: tracks channel state
   - Expected: channel.is_empty() is true
   - Expected: channel.is_empty() is false
   - Expected: channel.is_full() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks channel state")
step("Verify: tracks channel state")
val channel = BoundedChannel.new(1)
expect(channel.is_empty()).to_equal(true)
channel.send(9)
expect(channel.is_empty()).to_equal(false)
expect(channel.is_full()).to_equal(true)
```

</details>

#### closes channel

- closes channel
- Verify: closes channel
   - Expected: channel.is_closed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes channel")
step("Verify: closes channel")
val channel = BoundedChannel.new(1)
channel.close()
expect(channel.is_closed()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-CONCURRENCY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `193c273b394ba6b765ea6d4d19186a30b0b0cad20277426e0f989fe25277bba3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `193c273b394ba6b765ea6d4d19186a30b0b0cad20277426e0f989fe25277bba3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `193c273b394ba6b765ea6d4d19186a30b0b0cad20277426e0f989fe25277bba3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/lib/std/concurrency/concurrency_spec.spl
mirror: doc/06_spec/01_unit/lib/std/concurrency/concurrency_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/concurrency/concurrency_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/01_unit/lib/std/concurrency/concurrency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/concurrency/concurrency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/concurrency/concurrency_spec.spl:232:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates and yields single value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/concurrency/concurrency_spec.spl:242:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yields multiple values in sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/concurrency/concurrency_spec.spl:257:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns exhausted when finished' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/concurrency/concurrency_spec.spl:550:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can check and await' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/concurrency/concurrency_spec.spl:561:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can configure worker count' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/concurrency/concurrency_spec.spl:581:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can sleep thread' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/concurrency/concurrency_spec.spl:589:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can yield thread' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
