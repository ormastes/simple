# perf_optimization_spec

> Verifies the perf optimization behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# perf_optimization_spec

Verifies the perf optimization behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/perf_optimization_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the perf optimization behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### rt_thread_spawn_isolated - Closure Execution

#### basic closure execution

#### executes closure and returns result via join

- Verify: executes closure and returns result via join


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: executes closure and returns result via join")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: 42)
val result = handle.join()
expect result == 42
```

</details>

#### executes closure with arithmetic

- Verify: executes closure with arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: executes closure with arithmetic")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: 10 + 20 + 12)
val result = handle.join()
expect result == 42
```

</details>

#### executes closure with string result

- Verify: executes closure with string result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: executes closure with string result")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: "hello world")
val result = handle.join()
expect result == "hello world"
```

</details>

#### executes closure returning nil

- Verify: executes closure returning nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: executes closure returning nil")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: nil)
val result = handle.join()
expect result == nil
```

</details>

#### closure with captures

#### captures outer variable

- Verify: captures outer variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: captures outer variable")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val x = 100
val handle = spawn_thread(\: x + 1)
val result = handle.join()
expect result == 101
```

</details>

#### captures multiple variables

- Verify: captures multiple variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: captures multiple variables")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val a = 10
val b = 20
val c = 30
val handle = spawn_thread(\: a + b + c)
val result = handle.join()
expect result == 60
```

</details>

#### captures list and operates on it

- Verify: captures list and operates on it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: captures list and operates on it")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val items = [1, 2, 3, 4, 5]
val handle = spawn_thread(\: items.len())
val result = handle.join()
expect result == 5
```

</details>

#### unique handle IDs

#### assigns incrementing handle IDs

- Verify: assigns incrementing handle IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: assigns incrementing handle IDs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h1 = spawn_thread(\: 1)
val h2 = spawn_thread(\: 2)
val h3 = spawn_thread(\: 3)
expect h1.id() < h2.id()
expect h2.id() < h3.id()
h1.join()
h2.join()
h3.join()
```

</details>

#### handles are always positive

- Verify: handles are always positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: handles are always positive")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h = spawn_thread(\: nil)
expect h._handle >= 1
h.join()
```

</details>

#### thread is done after synchronous execution

#### reports done immediately for PureStd

- Verify: reports done immediately for PureStd


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: reports done immediately for PureStd")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: 42)
expect handle.is_done()
handle.join()
```

</details>

#### multiple spawns and joins

#### spawns 10 threads and joins all

- Verify: spawns 10 threads and joins all


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: spawns 10 threads and joins all")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var results = []
for i in 0..10:
    val handle = spawn_thread(\: i * i)
    results = results.push(handle.join())
expect results.len() == 10
```

</details>

#### spawns and joins in different order

- Verify: spawns and joins in different order


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: spawns and joins in different order")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h1 = spawn_thread(\: "first")
val h2 = spawn_thread(\: "second")
val h3 = spawn_thread(\: "third")
val r3 = h3.join()
val r1 = h1.join()
val r2 = h2.join()
expect r1 == "first"
expect r2 == "second"
expect r3 == "third"
```

</details>

### rt_thread_spawn_isolated_with_args - Explicit-arg Closure

#### basic explicit-argument execution

#### adds two numbers

- Verify: adds two numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: adds two numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread_with_args(5, 3) \x, y: x + y
val result = handle.join()
expect result == 8
```

</details>

#### concatenates strings

- Verify: concatenates strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: concatenates strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread_with_args("hello", " world") \a, b: a + b
val result = handle.join()
expect result == "hello world"
```

</details>

#### returns first argument

- Verify: returns first argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: returns first argument")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread_with_args(42, 99) \x, y: x
val result = handle.join()
expect result == 42
```

</details>

#### returns second argument

- Verify: returns second argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: returns second argument")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread_with_args(42, 99) \x, y: y
val result = handle.join()
expect result == 99
```

</details>

#### closure with channel communication

#### sends result via channel

- Verify: sends result via channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: sends result via channel")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
val handle = spawn_thread_with_args(6, ch._id) \data, channel_id:
    rt_channel_send(channel_id, data * 7)
    return nil

handle.join()
val result = ch.try_recv()
expect result == 42
ch.close()
```

</details>

#### sends multiple values via channel

- Verify: sends multiple values via channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: sends multiple values via channel")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
val handle = spawn_thread_with_args(3, ch._id) \count, channel_id:
    for i in 0..count:
        rt_channel_send(channel_id, i * 10)
    return nil

handle.join()
expect ch.try_recv() == 0
expect ch.try_recv() == 10
expect ch.try_recv() == 20
ch.close()
```

</details>

#### multiple explicit-argument spawns

#### runs 5 threads with accumulation

- Verify: runs 5 threads with accumulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: runs 5 threads with accumulation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var total = 0
for i in 0..5:
    val handle = spawn_thread_with_args(i, i + 1) \a, b: a * b
    total = total + handle.join()
# 0*1 + 1*2 + 2*3 + 3*4 + 4*5 = 0+2+6+12+20 = 40
expect total == 40
```

</details>

### Concurrent Backend Configuration

#### default backend

#### starts with pure_std

- Verify: starts with pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: starts with pure_std")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val backend = rt_get_concurrent_backend()
expect backend == "pure_std"
```

</details>

#### switching backends

#### switches to native and back

- Verify: switches to native and back


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: switches to native and back")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("native")
expect rt_get_concurrent_backend() == "native"
rt_set_concurrent_backend("pure_std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### accepts std as alias for pure_std

- Verify: accepts std as alias for pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: accepts std as alias for pure_std")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### accepts pure_std explicitly

- Verify: accepts pure_std explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: accepts pure_std explicitly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("pure_std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### thread operations work after backend switch

#### spawns thread after switching to native

- Verify: spawns thread after switching to native


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: spawns thread after switching to native")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("native")
val handle = spawn_thread(\: 42)
val result = handle.join()
expect result == 42
rt_set_concurrent_backend("pure_std")
```

</details>

#### channel works after switching to native

- Verify: channel works after switching to native


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: channel works after switching to native")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("native")
val ch = new_channel()
ch.send(100)
val result = ch.try_recv()
expect result == 100
ch.close()
rt_set_concurrent_backend("pure_std")
```

</details>

#### spawn_isolated_with_args works in native mode

- Verify: spawn_isolated_with_args works in native mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: spawn_isolated_with_args works in native mode")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("native")
val handle = spawn_thread_with_args(10, 5) \a, b: a - b
val result = handle.join()
expect result == 5
rt_set_concurrent_backend("pure_std")
```

</details>

#### round-trip backend switch

#### works after pure_std to native to pure_std

- Verify: works after pure_std to native to pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: works after pure_std to native to pure_std")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("native")
rt_set_concurrent_backend("pure_std")
val handle = spawn_thread(\: "survived")
expect handle.join() == "survived"
```

</details>

#### parallelism query per backend

#### reports parallelism in pure_std

- Verify: reports parallelism in pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: reports parallelism in pure_std")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("pure_std")
val cores = rt_thread_available_parallelism()
expect cores >= 1
```

</details>

#### reports parallelism in native

- Verify: reports parallelism in native


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: reports parallelism in native")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_set_concurrent_backend("native")
val cores = rt_thread_available_parallelism()
expect cores >= 1
rt_set_concurrent_backend("pure_std")
```

</details>

### Integration - Threads + Channels + Backend

#### producer-consumer pattern

#### thread produces main consumes

- Verify: thread produces main consumes


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: thread produces main consumes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
val handle = spawn_thread_with_args(ch._id, 5) \channel_id, count:
    for i in 0..count:
        rt_channel_send(channel_id, i * 10)
    return "done"

handle.join()

var sum = 0
for _ in 0..5:
    val v = ch.try_recv()
    if v != nil:
        sum = sum + v

expect sum == 100
ch.close()
```

</details>

#### fan-out pattern

#### spawns multiple threads writing to same channel

- Verify: spawns multiple threads writing to same channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: spawns multiple threads writing to same channel")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
var handles = []

for i in 0..5:
    val h = spawn_thread_with_args(i, ch._id) \data, channel_id:
        rt_channel_send(channel_id, data)
        return nil
    handles = handles.push(h)

for h in handles:
    h.join()

var received = []
for _ in 0..5:
    val v = ch.try_recv()
    if v != nil:
        received = received.push(v)

expect received.len() == 5
ch.close()
```

</details>

#### thread with complex captured data

#### captures dict and processes it

- Verify: captures dict and processes it


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: captures dict and processes it")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val data = {"a": 1, "b": 2, "c": 3}
val handle = spawn_thread_with_args(data, nil) \d, _:
    var total = 0
    for k in d.keys():
        total = total + d[k]
    return total

val result = handle.join()
expect result == 6
```

</details>

#### captures list and computes sum

- Verify: captures list and computes sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: captures list and computes sum")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val handle = spawn_thread_with_args(numbers, nil) \nums, _:
    var sum = 0
    for n in nums:
        sum = sum + n
    return sum

expect handle.join() == 55
```

</details>

#### backend switch during active work

#### completes work switches continues

- Verify: completes work switches continues


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: completes work switches continues")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h1 = spawn_thread(\: "pure_std_result")
expect h1.join() == "pure_std_result"

rt_set_concurrent_backend("native")
val h2 = spawn_thread(\: "native_result")
expect h2.join() == "native_result"

rt_set_concurrent_backend("pure_std")
val h3 = spawn_thread(\: "back_to_std")
expect h3.join() == "back_to_std"
```

</details>

### Stress Tests

#### many thread spawns

#### spawns and joins 50 threads

- Verify: spawns and joins 50 threads


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: spawns and joins 50 threads")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var results = []
for i in 0..50:
    val h = spawn_thread(\: i)
    results = results.push(h.join())
expect results.len() == 50
```

</details>

#### spawns 50 explicit-argument threads

- Verify: spawns 50 explicit-argument threads


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: spawns 50 explicit-argument threads")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var total = 0
for i in 0..50:
    val h = spawn_thread_with_args(i, 1) \a, b: a + b
    total = total + h.join()
# Sum of (i+1) for i in 0..50 = 0+1+1+2+1+3+...+1+50 = sum(1..51) = 1275
expect total == 1275
```

</details>

#### many channel operations

#### sends and receives 100 messages

- Verify: sends and receives 100 messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: sends and receives 100 messages")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
for i in 0..100:
    ch.send(i)

var sum = 0
for _ in 0..100:
    sum = sum + ch.try_recv()

expect sum == 4950
ch.close()
```

</details>

#### creates and closes 20 channels

- Verify: creates and closes 20 channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: creates and closes 20 channels")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var channels = []
for _ in 0..20:
    channels = channels.push(new_channel())

for ch in channels:
    ch.send(42)

for ch in channels:
    expect ch.try_recv() == 42
    ch.close()

for ch in channels:
    expect ch.is_closed()
```

</details>

#### thread spawn with channel stress

#### 10 threads each send 5 messages

- Verify: 10 threads each send 5 messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: 10 threads each send 5 messages")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
var handles = []

for i in 0..10:
    val h = spawn_thread_with_args(i, ch._id) \thread_num, channel_id:
        for j in 0..5:
            rt_channel_send(channel_id, thread_num * 100 + j)
        return nil
    handles = handles.push(h)

for h in handles:
    h.join()

var count = 0
var msg = ch.try_recv()
while msg != nil:
    count = count + 1
    msg = ch.try_recv()

expect count == 50
ch.close()
```

</details>

#### rapid backend switching under load

#### alternates backends 10 times with spawns

- Verify: alternates backends 10 times with spawns


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: alternates backends 10 times with spawns")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
for round in 0..10:
    if round % 2 == 0:
        rt_set_concurrent_backend("pure_std")
    else:
        rt_set_concurrent_backend("native")

    val h = spawn_thread(\: round)
    expect h.join() == round

rt_set_concurrent_backend("pure_std")
```

</details>

#### thread free cleanup

#### frees 20 handles without error

- Verify: frees 20 handles without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: frees 20 handles without error")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
for i in 0..20:
    val h = spawn_thread(\: i)
    h.join()
    rt_thread_free(h._handle)
```

</details>

### Edge Cases

#### closure returning complex types

#### returns a list

- Verify: returns a list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: returns a list")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: [1, 2, 3])
val result = handle.join()
expect result == [1, 2, 3]
```

</details>

#### returns a dict

- Verify: returns a dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: returns a dict")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: {"key": "value"})
val result = handle.join()
expect result["key"] == "value"
```

</details>

#### returns nested structure

- Verify: returns nested structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: returns nested structure")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: {"nums": [1, 2, 3], "name": "test"})
val result = handle.join()
expect result["nums"].len() == 3
expect result["name"] == "test"
```

</details>

#### closure with empty body

#### returns nil for empty closure

- Verify: returns nil for empty closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: returns nil for empty closure")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread(\: nil)
expect handle.join() == nil
```

</details>

#### channel edge cases

#### try_recv on empty channel returns nil

- Verify: try_recv on empty channel returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: try_recv on empty channel returns nil")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
val result = ch.try_recv()
expect result == nil
ch.close()
```

</details>

#### is_closed after close

- Verify: is_closed after close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: is_closed after close")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val ch = new_channel()
expect not ch.is_closed()
ch.close()
expect ch.is_closed()
```

</details>

#### thread yield and sleep

#### yield does not crash

- Verify: yield does not crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: yield does not crash")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_thread_yield()
expect true
```

</details>

#### sleep for 1ms does not crash

- Verify: sleep for 1ms does not crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: sleep for 1ms does not crash")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
rt_thread_sleep(1)
expect true
```

</details>

#### spawn_isolated with no extra args

#### closure with no parameters works

- Verify: closure with no parameters works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: closure with no parameters works")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h = spawn_thread(\: 99)
expect h.join() == 99
```

</details>

#### spawn_thread_with_args with nil arguments

#### handles nil data arguments

- Verify: handles nil data arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_PERF_OPTIMIZATION-001
step("Verify: handles nil data arguments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val handle = spawn_thread_with_args(nil, nil) \a, b: "ok"
expect handle.join() == "ok"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4a696058f59f3983bf5fd8a204f8244bd93676d5cda280adb4b21cb46c801e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4a696058f59f3983bf5fd8a204f8244bd93676d5cda280adb4b21cb46c801e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4a696058f59f3983bf5fd8a204f8244bd93676d5cda280adb4b21cb46c801e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/perf_optimization_spec.spl
mirror: doc/06_spec/01_unit/std/perf_optimization_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/perf_optimization_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/perf_optimization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/perf_optimization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
