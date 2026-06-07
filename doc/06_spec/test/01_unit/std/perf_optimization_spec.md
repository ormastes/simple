# Performance Optimization Specification

> Intensive tests for performance optimization changes: 1. rt_thread_spawn_isolated closure execution (was stub) 2. rt_set_concurrent_backend / rt_get_concurrent_backend FFI 3. Integration: concurrent backend + thread spawn + channels

<!-- sdn-diagram:id=perf_optimization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=perf_optimization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

perf_optimization_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=perf_optimization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Performance Optimization Specification

Intensive tests for performance optimization changes: 1. rt_thread_spawn_isolated closure execution (was stub) 2. rt_set_concurrent_backend / rt_get_concurrent_backend FFI 3. Integration: concurrent backend + thread spawn + channels

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #perf-001 through #perf-003 |
| Category | Runtime \| Infrastructure |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/01_unit/std/perf_optimization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Intensive tests for performance optimization changes:
1. rt_thread_spawn_isolated closure execution (was stub)
2. rt_set_concurrent_backend / rt_get_concurrent_backend FFI
3. Integration: concurrent backend + thread spawn + channels

## Key Concepts

| Concept | Description |
|---------|-------------|
| Backend switching | PureStd (single-thread) vs Native (concurrent crates) |
| Closure execution | rt_thread_spawn_isolated now evaluates closure body |
| Channel communication | Threads can send/receive values via channels |

## Scenarios

### rt_thread_spawn_isolated - Closure Execution

#### basic closure execution

#### executes closure and returns result via join

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: 42)
val result = handle.join()
expect result == 42
```

</details>

#### executes closure with arithmetic

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: 10 + 20 + 12)
val result = handle.join()
expect result == 42
```

</details>

#### executes closure with string result

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: "hello world")
val result = handle.join()
expect result == "hello world"
```

</details>

#### executes closure returning nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: nil)
val result = handle.join()
expect result == nil
```

</details>

#### closure with captures

#### captures outer variable

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
val handle = spawn_thread(\: x + 1)
val result = handle.join()
expect result == 101
```

</details>

#### captures multiple variables

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = 30
val handle = spawn_thread(\: a + b + c)
val result = handle.join()
expect result == 60
```

</details>

#### captures list and operates on it

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
val handle = spawn_thread(\: items.len())
val result = handle.join()
expect result == 5
```

</details>

#### unique handle IDs

#### assigns incrementing handle IDs

1. expect h1 id

2. expect h2 id

3. h1 join

4. h2 join

5. h3 join


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. h join


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = spawn_thread(\: nil)
expect h._handle >= 1
h.join()
```

</details>

#### thread is done after synchronous execution

#### reports done immediately for PureStd

1. expect handle is done

2. handle join


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: 42)
expect handle.is_done()
handle.join()
```

</details>

#### multiple spawns and joins

#### spawns 10 threads and joins all

1. results = results push

2. expect results len


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = []
for i in 0..10:
    val handle = spawn_thread(\: i * i)
    results = results.push(handle.join())
expect results.len() == 10
```

</details>

#### spawns and joins in different order

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

### rt_thread_spawn_isolated_with_args - Two-arg Closure

#### basic two-arg execution

#### adds two numbers

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread_with_args(5, 3) \x, y: x + y
val result = handle.join()
expect result == 8
```

</details>

#### concatenates strings

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread_with_args("hello", " world") \a, b: a + b
val result = handle.join()
expect result == "hello world"
```

</details>

#### returns first argument

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread_with_args(42, 99) \x, y: x
val result = handle.join()
expect result == 42
```

</details>

#### returns second argument

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread_with_args(42, 99) \x, y: y
val result = handle.join()
expect result == 99
```

</details>

#### closure with channel communication

#### sends result via channel

1. rt channel send

2. handle join

3. ch close


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rt channel send

2. handle join

3. expect ch try recv

4. expect ch try recv

5. expect ch try recv

6. ch close


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### multiple two-arg spawns

#### runs 5 threads with accumulation

1. total = total + handle join


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = rt_get_concurrent_backend()
expect backend == "pure_std"
```

</details>

#### switching backends

#### switches to native and back

1. rt set concurrent backend

2. expect rt get concurrent backend

3. rt set concurrent backend

4. expect rt get concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("native")
expect rt_get_concurrent_backend() == "native"
rt_set_concurrent_backend("pure_std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### accepts std as alias for pure_std

1. rt set concurrent backend

2. expect rt get concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### accepts pure_std explicitly

1. rt set concurrent backend

2. expect rt get concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("pure_std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### thread operations work after backend switch

#### spawns thread after switching to native

1. rt set concurrent backend

2. rt set concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("native")
val handle = spawn_thread(\: 42)
val result = handle.join()
expect result == 42
rt_set_concurrent_backend("pure_std")
```

</details>

#### channel works after switching to native

1. rt set concurrent backend

2. ch send

3. ch close

4. rt set concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rt set concurrent backend

2. rt set concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("native")
val handle = spawn_thread_with_args(10, 5) \a, b: a - b
val result = handle.join()
expect result == 5
rt_set_concurrent_backend("pure_std")
```

</details>

#### round-trip backend switch

#### works after pure_std to native to pure_std

1. rt set concurrent backend

2. rt set concurrent backend

3. expect handle join


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("native")
rt_set_concurrent_backend("pure_std")
val handle = spawn_thread(\: "survived")
expect handle.join() == "survived"
```

</details>

#### parallelism query per backend

#### reports parallelism in pure_std

1. rt set concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("pure_std")
val cores = rt_thread_available_parallelism()
expect cores >= 1
```

</details>

#### reports parallelism in native

1. rt set concurrent backend

2. rt set concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_set_concurrent_backend("native")
val cores = rt_thread_available_parallelism()
expect cores >= 1
rt_set_concurrent_backend("pure_std")
```

</details>

### Integration - Threads + Channels + Backend

#### producer-consumer pattern

#### thread produces main consumes

1. rt channel send

2. handle join

3. ch close


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rt channel send

2. handles = handles push

3. h join

4. received = received push

5. expect received len

6. ch close


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect handle join


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect h1 join

2. rt set concurrent backend

3. expect h2 join

4. rt set concurrent backend

5. expect h3 join


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. results = results push

2. expect results len


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = []
for i in 0..50:
    val h = spawn_thread(\: i)
    results = results.push(h.join())
expect results.len() == 50
```

</details>

#### spawns 50 two-arg threads

1. total = total + h join


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. ch send

2. sum = sum + ch try recv

3. ch close


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. channels = channels push

2. ch send

3. expect ch try recv

4. ch close

5. expect ch is closed


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rt channel send

2. handles = handles push

3. h join

4. var msg = ch try recv

5. msg = ch try recv

6. ch close


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. rt set concurrent backend

2. rt set concurrent backend

3. expect h join

4. rt set concurrent backend


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. h join

2. rt thread free


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..20:
    val h = spawn_thread(\: i)
    h.join()
    rt_thread_free(h._handle)
```

</details>

### Edge Cases

#### closure returning complex types

#### returns a list

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: [1, 2, 3])
val result = handle.join()
expect result == [1, 2, 3]
```

</details>

#### returns a dict

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: {"key": "value"})
val result = handle.join()
expect result["key"] == "value"
```

</details>

#### returns nested structure

1. expect result["nums"] len


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: {"nums": [1, 2, 3], "name": "test"})
val result = handle.join()
expect result["nums"].len() == 3
expect result["name"] == "test"
```

</details>

#### closure with empty body

#### returns nil for empty closure

1. expect handle join


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = spawn_thread(\: nil)
expect handle.join() == nil
```

</details>

#### channel edge cases

#### try_recv on empty channel returns nil

1. ch close


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = new_channel()
val result = ch.try_recv()
expect result == nil
ch.close()
```

</details>

#### is_closed after close

1. expect not ch is closed

2. ch close

3. expect ch is closed


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = new_channel()
expect not ch.is_closed()
ch.close()
expect ch.is_closed()
```

</details>

#### thread yield and sleep

#### yield does not crash

1. rt thread yield


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_thread_yield()
expect true
```

</details>

#### sleep for 1ms does not crash

1. rt thread sleep


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_thread_sleep(1)
expect true
```

</details>

#### spawn_isolated with no extra args

#### closure with no parameters works

1. expect h join


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = spawn_thread(\: 99)
expect h.join() == 99
```

</details>

#### spawn_thread_with_args with nil arguments

#### handles nil data arguments

1. expect handle join


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
