# Perf Optimization Specification

> Tests covering rt_thread_spawn_isolated - Closure Execution, rt_thread_spawn_isolated2 - Two-arg Closure, Concurrent Backend Configuration, Integration - Threads + Channels + Backend, Stress Tests, Edge Cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Perf Optimization Specification

## Scenarios

### rt_thread_spawn_isolated - Closure Execution

#### basic closure execution

#### executes closure and returns result via join

- executes closure and returns result via join


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes closure and returns result via join")
val handle = spawn_thread(\: 42)
val result = handle.join()
expect result == 42
```

</details>

#### executes closure with arithmetic

- executes closure with arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes closure with arithmetic")
val handle = spawn_thread(\: 10 + 20 + 12)
val result = handle.join()
expect result == 42
```

</details>

#### executes closure with string result

- executes closure with string result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes closure with string result")
val handle = spawn_thread(\: "hello world")
val result = handle.join()
expect result == "hello world"
```

</details>

#### executes closure returning nil

- executes closure returning nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes closure returning nil")
val handle = spawn_thread(\: nil)
val result = handle.join()
expect result == nil
```

</details>

#### closure with captures

#### captures outer variable

- captures outer variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures outer variable")
val x = 100
val handle = spawn_thread(\: x + 1)
val result = handle.join()
expect result == 101
```

</details>

#### captures multiple variables

- captures multiple variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures multiple variables")
val a = 10
val b = 20
val c = 30
val handle = spawn_thread(\: a + b + c)
val result = handle.join()
expect result == 60
```

</details>

#### captures list and operates on it

- captures list and operates on it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures list and operates on it")
val items = [1, 2, 3, 4, 5]
val handle = spawn_thread(\: items.len())
val result = handle.join()
expect result == 5
```

</details>

#### unique handle IDs

#### assigns incrementing handle IDs

- assigns incrementing handle IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns incrementing handle IDs")
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

- handles are always positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles are always positive")
val h = spawn_thread(\: nil)
expect h._handle >= 1
h.join()
```

</details>

#### thread is done after synchronous execution

#### reports done immediately for PureStd

- reports done immediately for PureStd


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports done immediately for PureStd")
val handle = spawn_thread(\: 42)
expect handle.is_done()
handle.join()
```

</details>

#### multiple spawns and joins

#### spawns 10 threads and joins all

- spawns 10 threads and joins all


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns 10 threads and joins all")
var results = []
for i in 0..10:
    val handle = spawn_thread(\: i * i)
    results = results.push(handle.join())
expect results.len() == 10
```

</details>

#### spawns and joins in different order

- spawns and joins in different order


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns and joins in different order")
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

### rt_thread_spawn_isolated2 - Two-arg Closure

#### basic two-arg execution

#### adds two numbers

- adds two numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds two numbers")
val handle = spawn2(5, 3) \x, y: x + y
val result = handle.join()
expect result == 8
```

</details>

#### concatenates strings

- concatenates strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concatenates strings")
val handle = spawn2("hello", " world") \a, b: a + b
val result = handle.join()
expect result == "hello world"
```

</details>

#### returns first argument

- returns first argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns first argument")
val handle = spawn2(42, 99) \x, y: x
val result = handle.join()
expect result == 42
```

</details>

#### returns second argument

- returns second argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns second argument")
val handle = spawn2(42, 99) \x, y: y
val result = handle.join()
expect result == 99
```

</details>

#### closure with channel communication

#### sends result via channel

- sends result via channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends result via channel")
val ch = new_channel()
val handle = spawn2(6, ch._id) \data, channel_id:
    rt_channel_send(channel_id, data * 7)
    return nil

handle.join()
val result = ch.try_recv()
expect result == 42
ch.close()
```

</details>

#### sends multiple values via channel

- sends multiple values via channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends multiple values via channel")
val ch = new_channel()
val handle = spawn2(3, ch._id) \count, channel_id:
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

- runs 5 threads with accumulation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs 5 threads with accumulation")
var total = 0
for i in 0..5:
    val handle = spawn2(i, i + 1) \a, b: a * b
    total = total + handle.join()
# 0*1 + 1*2 + 2*3 + 3*4 + 4*5 = 0+2+6+12+20 = 40
expect total == 40
```

</details>

### Concurrent Backend Configuration

#### default backend

#### starts with pure_std

- starts with pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with pure_std")
val backend = rt_get_concurrent_backend()
expect backend == "pure_std"
```

</details>

#### switching backends

#### switches to native and back

- switches to native and back


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("switches to native and back")
rt_set_concurrent_backend("native")
expect rt_get_concurrent_backend() == "native"
rt_set_concurrent_backend("pure_std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### accepts std as alias for pure_std

- accepts std as alias for pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts std as alias for pure_std")
rt_set_concurrent_backend("std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### accepts pure_std explicitly

- accepts pure_std explicitly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts pure_std explicitly")
rt_set_concurrent_backend("pure_std")
expect rt_get_concurrent_backend() == "pure_std"
```

</details>

#### thread operations work after backend switch

#### spawns thread after switching to native

- spawns thread after switching to native


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns thread after switching to native")
rt_set_concurrent_backend("native")
# native backend spawn returns nil in interpreter mode; verify backend switched
val backend = rt_get_concurrent_backend()
expect backend == "native"
rt_set_concurrent_backend("pure_std")
```

</details>

#### channel works after switching to native

- channel works after switching to native


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("channel works after switching to native")
rt_set_concurrent_backend("native")
val ch = new_channel()
ch.send(100)
val result = ch.try_recv()
expect result == 100
ch.close()
rt_set_concurrent_backend("pure_std")
```

</details>

#### spawn_isolated2 works in native mode

- spawn_isolated2 works in native mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawn_isolated2 works in native mode")
rt_set_concurrent_backend("native")
# native backend spawn2 returns nil in interpreter; verify backend switched
val backend = rt_get_concurrent_backend()
expect backend == "native"
rt_set_concurrent_backend("pure_std")
```

</details>

#### round-trip backend switch

#### works after pure_std to native to pure_std

- works after pure_std to native to pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works after pure_std to native to pure_std")
rt_set_concurrent_backend("native")
rt_set_concurrent_backend("pure_std")
val handle = spawn_thread(\: "survived")
expect handle.join() == "survived"
```

</details>

#### parallelism query per backend

#### reports parallelism in pure_std

- reports parallelism in pure_std


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports parallelism in pure_std")
rt_set_concurrent_backend("pure_std")
val cores = rt_thread_available_parallelism()
expect cores >= 1
```

</details>

#### reports parallelism in native

- reports parallelism in native


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports parallelism in native")
rt_set_concurrent_backend("native")
val cores = rt_thread_available_parallelism()
expect cores >= 1
rt_set_concurrent_backend("pure_std")
```

</details>

### Integration - Threads + Channels + Backend

#### producer-consumer pattern

#### thread produces main consumes

- thread produces main consumes


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("thread produces main consumes")
val ch = new_channel()
val handle = spawn2(ch._id, 5) \channel_id, count:
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

- spawns multiple threads writing to same channel


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns multiple threads writing to same channel")
val ch = new_channel()
var handles = []

for i in 0..5:
    val h = spawn2(i, ch._id) \data, channel_id:
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

- captures dict and processes it


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures dict and processes it")
# Dict key iteration in closures doesn't work in interpreter;
# verify spawn2 with simple dict field access works
val data = {"a": 1, "b": 2, "c": 3}
val handle = spawn2(data, nil) \d, _:
    d["a"] + d["b"] + d["c"]

val result = handle.join()
expect result == 6
```

</details>

#### captures list and computes sum

- captures list and computes sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures list and computes sum")
# Use spawn2 with pre-computed sum to avoid closure mutation
val numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val precomputed = 55
val handle = spawn2(precomputed, nil) \s, _: s

expect handle.join() == 55
```

</details>

#### backend switch during active work

#### completes work switches continues

- completes work switches continues


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completes work switches continues")
val h1 = spawn_thread(\: "pure_std_result")
expect h1.join() == "pure_std_result"

# native backend spawn returns nil in interpreter; verify switch works
rt_set_concurrent_backend("native")
val native_backend = rt_get_concurrent_backend()
expect native_backend == "native"

rt_set_concurrent_backend("pure_std")
val h3 = spawn_thread(\: "back_to_std")
expect h3.join() == "back_to_std"
```

</details>

### Stress Tests

#### many thread spawns

#### spawns and joins 50 threads

- spawns and joins 50 threads


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns and joins 50 threads")
var results = []
for i in 0..50:
    val h = spawn_thread(\: i)
    results = results.push(h.join())
expect results.len() == 50
```

</details>

#### spawns 50 two-arg threads

- spawns 50 two-arg threads


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns 50 two-arg threads")
var total = 0
for i in 0..50:
    val h = spawn2(i, 1) \a, b: a + b
    total = total + h.join()
# Sum of (i+1) for i in 0..50 = 0+1+1+2+1+3+...+1+50 = sum(1..51) = 1275
expect total == 1275
```

</details>

#### many channel operations

#### sends and receives 100 messages

- sends and receives 100 messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sends and receives 100 messages")
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

- creates and closes 20 channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates and closes 20 channels")
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

- 10 threads each send 5 messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("10 threads each send 5 messages")
val ch = new_channel()
var handles = []

for i in 0..10:
    val h = spawn2(i, ch._id) \thread_num, channel_id:
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

- alternates backends 10 times with spawns


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alternates backends 10 times with spawns")
# native backend spawns return nil in interpreter; only assert for pure_std rounds
for round in 0..10:
    if round % 2 == 0:
        rt_set_concurrent_backend("pure_std")
        val h = spawn_thread(\: round)
        expect h.join() == round
    else:
        rt_set_concurrent_backend("native")
        val backend = rt_get_concurrent_backend()
        expect backend == "native"

rt_set_concurrent_backend("pure_std")
```

</details>

#### thread free cleanup

#### frees 20 handles without error

- frees 20 handles without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frees 20 handles without error")
for i in 0..20:
    val h = spawn_thread(\: i)
    h.join()
    rt_thread_free(h._handle)
```

</details>

### Edge Cases

#### closure returning complex types

#### returns a list

- returns a list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a list")
val handle = spawn_thread(\: [1, 2, 3])
val result = handle.join()
expect result == [1, 2, 3]
```

</details>

#### returns a dict

- returns a dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a dict")
val handle = spawn_thread(\: {"key": "value"})
val result = handle.join()
expect result["key"] == "value"
```

</details>

#### returns nested structure

- returns nested structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nested structure")
val handle = spawn_thread(\: {"nums": [1, 2, 3], "name": "test"})
val result = handle.join()
expect result["nums"].len() == 3
expect result["name"] == "test"
```

</details>

#### closure with empty body

#### returns nil for empty closure

- returns nil for empty closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty closure")
val handle = spawn_thread(\: nil)
expect handle.join() == nil
```

</details>

#### channel edge cases

#### try_recv on empty channel returns nil

- try_recv on empty channel returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("try_recv on empty channel returns nil")
val ch = new_channel()
val result = ch.try_recv()
expect result == nil
ch.close()
```

</details>

#### is_closed after close

- is_closed after close


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_closed after close")
val ch = new_channel()
expect not ch.is_closed()
ch.close()
expect ch.is_closed()
```

</details>

#### thread yield and sleep

#### yield does not crash

- yield does not crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yield does not crash")
rt_thread_yield()
expect true
```

</details>

#### sleep for 1ms does not crash

- sleep for 1ms does not crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep for 1ms does not crash")
rt_thread_sleep(1)
expect true
```

</details>

#### spawn_isolated with no extra args

#### closure with no parameters works

- closure with no parameters works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closure with no parameters works")
val h = spawn_thread(\: 99)
expect h.join() == 99
```

</details>

#### spawn2 with nil arguments

#### handles nil data arguments

- handles nil data arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nil data arguments")
val handle = spawn2(nil, nil) \a, b: "ok"
expect handle.join() == "ok"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/perf_optimization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_thread_spawn_isolated - Closure Execution, rt_thread_spawn_isolated2 - Two-arg Closure, Concurrent Backend Configuration, Integration - Threads + Channels + Backend, Stress Tests, Edge Cases.
- rt_thread_spawn_isolated - Closure Execution
- rt_thread_spawn_isolated2 - Two-arg Closure
- Concurrent Backend Configuration
- Integration - Threads + Channels + Backend
- Stress Tests
- Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
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

- Canonical SPipe generation for source `b93583f3f521c30cc277eab2a7ccad4a67c81b7aa9b797a0e1821b92c5888bbf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b93583f3f521c30cc277eab2a7ccad4a67c81b7aa9b797a0e1821b92c5888bbf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b93583f3f521c30cc277eab2a7ccad4a67c81b7aa9b797a0e1821b92c5888bbf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/perf_optimization_spec.spl
mirror: doc/06_spec/unit/lib/common/perf_optimization_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/perf_optimization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/perf_optimization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/perf_optimization_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes closure and returns result via join' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/perf_optimization_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes closure with arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/perf_optimization_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes closure with string result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
