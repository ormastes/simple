# Async/Promise System Tests

> End-to-end system tests verifying complete async workflows combining promises, futures, channels, combinators, and work-stealing queues. These tests verify components work together, not in isolation.

<!-- sdn-diagram:id=async_promise_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_promise_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_promise_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_promise_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async/Promise System Tests

End-to-end system tests verifying complete async workflows combining promises, futures, channels, combinators, and work-stealing queues. These tests verify components work together, not in isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | doc/requirement/async_promise_intensive_tests.md |
| Plan | doc/03_plan/async_promise_intensive_tests.md |
| Design | doc/05_design/async_promise_intensive_tests.md |
| Source | `test/03_system/stdlib/async_promise_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
End-to-end system tests verifying complete async workflows combining
promises, futures, channels, combinators, and work-stealing queues.
These tests verify components work together, not in isolation.

## Scenarios

### Promise Creation and Resolution

#### should create a pending promise and resolve it

1. var p = Promise
   - Expected: p.is_pending() is true
   - Expected: p.is_resolved() is false
2. p resolve
   - Expected: p.is_resolved() is true
   - Expected: p.is_pending() is false
   - Expected: p.value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Pending)
expect(p.is_pending()).to_equal(true)
expect(p.is_resolved()).to_equal(false)

p.resolve(42)
expect(p.is_resolved()).to_equal(true)
expect(p.is_pending()).to_equal(false)
expect(p.value()).to_equal(42)
```

</details>

#### should create a pending promise and reject it

1. var p = Promise
2. p reject
   - Expected: p.is_rejected() is true
   - Expected: p.error() equals `something went wrong`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Pending)
p.reject("something went wrong")
expect(p.is_rejected()).to_equal(true)
expect(p.error()).to_equal("something went wrong")
```

</details>

### Promise-to-Future Data Flow

#### should flow data from promise resolution through to future completion

1. var p = Promise
2. var future = future pending
   - Expected: p.is_resolved() is true
3. future complete
   - Expected: "promise should already be resolved" equals ``
   - Expected: future.is_ready() is true
   - Expected: future.value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Resolved(42))
var future = future_pending()

expect(p.is_resolved()).to_equal(true)
match p.state:
    case Resolved(v):
        future.complete(v)
    case _:
        expect("promise should already be resolved").to_equal("")
expect(future.is_ready()).to_equal(true)
expect(future.value()).to_equal(42)
```

</details>

#### should flow rejection from promise to failed future

1. var p = Promise
2. p reject
3. var future = future failed
   - Expected: future.is_failed() is true
   - Expected: future.error() equals `upstream error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Pending)
p.reject("upstream error")

var future = future_failed(p.error())
expect(future.is_failed()).to_equal(true)
expect(future.error()).to_equal("upstream error")
```

</details>

### Channel Producer-Consumer

#### should deliver all messages from producer to consumer in order

1. var ch = Channel
   - Expected: ch.size() equals `5`
2. var r0 = ch receive
3. var r1 = ch receive
4. var r2 = ch receive
5. var r3 = ch receive
6. var r4 = ch receive
   - Expected: r0 equals `0`
   - Expected: r1 equals `10`
   - Expected: r2 equals `20`
   - Expected: r3 equals `30`
   - Expected: r4 equals `40`
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel(buffer: [0, 10, 20, 30, 40], closed: false, count: 5)

expect(ch.size()).to_equal(5)

var r0 = ch.receive()
var r1 = ch.receive()
var r2 = ch.receive()
var r3 = ch.receive()
var r4 = ch.receive()
expect(r0).to_equal(0)
expect(r1).to_equal(10)
expect(r2).to_equal(20)
expect(r3).to_equal(30)
expect(r4).to_equal(40)
expect(ch.is_empty()).to_equal(true)
```

</details>

#### should return nil when receiving from empty channel

1. var ch = Channel
2. var result = ch receive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel(buffer: [], closed: false, count: 0)
var result = ch.receive()
expect(result).to_be_nil()
```

</details>

### Future Combinators - join_all and select

#### should join all ready futures into a single result list

1. var f1 = future ready
2. var f2 = future ready
3. var f3 = future ready
4. var joined = join all futures
   - Expected: joined.is_ready() is true
5. var vals = joined value
   - Expected: vals.len() equals `3`
   - Expected: vals[0] equals `10`
   - Expected: vals[1] equals `20`
   - Expected: vals[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = future_ready(10)
var f2 = future_ready(20)
var f3 = future_ready(30)

var joined = join_all_futures([f1, f2, f3])
expect(joined.is_ready()).to_equal(true)
var vals = joined.value()
expect(vals.len()).to_equal(3)
expect(vals[0]).to_equal(10)
expect(vals[1]).to_equal(20)
expect(vals[2]).to_equal(30)
```

</details>

#### should select the first ready future from a mixed set

1. var f1 = future pending
2. var f2 = future ready
3. var f3 = future pending
4. var selected = select first future
   - Expected: selected.is_ready() is true
   - Expected: selected.value() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = future_pending()
var f2 = future_ready(99)
var f3 = future_pending()

var selected = select_first_future([f1, f2, f3])
expect(selected.is_ready()).to_equal(true)
expect(selected.value()).to_equal(99)
```

</details>

### Error Propagation

#### should propagate rejection from promise through future to combinator

1. var p = Promise
2. p reject
   - Expected: p.is_rejected() is true
3. var failed future = future failed
   - Expected: failed_future.is_failed() is true
   - Expected: failed_future.error() equals `upstream failure`
4. var f ok = future ready
5. var joined = join all futures
   - Expected: joined.is_failed() is true
   - Expected: joined.error() equals `upstream failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = Promise(state: PromiseState.Pending)
p.reject("upstream failure")
expect(p.is_rejected()).to_equal(true)

var failed_future = future_failed(p.error())
expect(failed_future.is_failed()).to_equal(true)
expect(failed_future.error()).to_equal("upstream failure")

var f_ok = future_ready(100)
var joined = join_all_futures([f_ok, failed_future])
expect(joined.is_failed()).to_equal(true)
expect(joined.error()).to_equal("upstream failure")
```

</details>

### Work-Stealing Queue Distribution

#### should distribute and steal tasks across worker queues

1. var wsq = WorkStealingQueue
2. wsq push
3. wsq push
4. wsq push
5. wsq push
   - Expected: wsq.total_tasks() equals `4`
6. var stolen = wsq steal
   - Expected: stolen equals `10`
7. var own = wsq pop
   - Expected: own equals `30`
   - Expected: wsq.total_tasks() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wsq = WorkStealingQueue(q0: [], q1: [], q2: [])

wsq.push(0, 10)
wsq.push(0, 20)
wsq.push(0, 30)
wsq.push(1, 40)

expect(wsq.total_tasks()).to_equal(4)

# Worker 2 steals from worker 0 (takes from front)
var stolen = wsq.steal(from_id: 0)
expect(stolen).to_equal(10)

# Worker 0 pops from own queue (takes from back)
var own = wsq.pop(worker_id: 0)
expect(own).to_equal(30)

expect(wsq.total_tasks()).to_equal(2)
```

</details>

#### should return nil when stealing from empty queue

1. var wsq = WorkStealingQueue
2. var result = wsq steal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wsq = WorkStealingQueue(q0: [], q1: [], q2: [])
var result = wsq.steal(from_id: 0)
expect(result).to_be_nil()
```

</details>

### Promise Chaining

#### should chain multiple promise resolutions producing correct final result

1. var p1 = Promise
2. var p2 = Promise
3. var p3 = Promise
4. p1 resolve
5. var v1 = p1 value
6. p2 resolve
7. var v2 = p2 value
8. p3 resolve
   - Expected: p1.value() equals `5`
   - Expected: p2.value() equals `15`
   - Expected: p3.value() equals `30`
   - Expected: p3.is_resolved() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Without function-typed fields, we chain manually
var p1 = Promise(state: PromiseState.Pending)
var p2 = Promise(state: PromiseState.Pending)
var p3 = Promise(state: PromiseState.Pending)

# Step 1: resolve p1 with initial value
p1.resolve(5)

# Step 2: transform and resolve p2
var v1 = p1.value()
p2.resolve(v1 + 10)

# Step 3: transform and resolve p3
var v2 = p2.value()
p3.resolve(v2 * 2)

expect(p1.value()).to_equal(5)
expect(p2.value()).to_equal(15)
expect(p3.value()).to_equal(30)
expect(p3.is_resolved()).to_equal(true)
```

</details>

### Mixed Ready and Pending Futures

#### should handle join_all with all ready futures

1. future ready
2. future ready
3. future ready
4. var joined = join all futures
   - Expected: joined.is_ready() is true
5. var vals = joined value
   - Expected: vals.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var futures = [
    future_ready(1),
    future_ready(2),
    future_ready(3)
]
var joined = join_all_futures(futures)
expect(joined.is_ready()).to_equal(true)
var vals = joined.value()
expect(vals.len()).to_equal(3)
```

</details>

#### should select first ready from mixed ready/pending set

1. future pending
2. future pending
3. future ready
4. future pending
5. var result = select first future
   - Expected: result.is_ready() is true
   - Expected: result.value() equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var futures = [
    future_pending(),
    future_pending(),
    future_ready(77),
    future_pending()
]
var result = select_first_future(futures)
expect(result.is_ready()).to_equal(true)
expect(result.value()).to_equal(77)
```

</details>

#### should return pending when no futures are ready

1. future pending
2. future pending
3. var result = select first future
   - Expected: result.is_ready() is false
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var futures = [
    future_pending(),
    future_pending()
]
var result = select_first_future(futures)
expect(result.is_ready()).to_equal(false)
expect(result.is_pending()).to_equal(true)
```

</details>

### Channel Close Semantics

#### should stop accepting messages after channel is closed

1. var ch = TextChannel
2. ch send
3. ch close
4. ch send
   - Expected: ch.size() equals `1`
   - Expected: ch.receive() equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = TextChannel(buffer: [], closed: false, count: 0)
ch.send("before")
ch.close()
ch.send("after")
expect(ch.size()).to_equal(1)
expect(ch.receive()).to_equal("before")
```

</details>

#### should drain remaining messages after close

1. var ch = Channel
2. ch send
3. ch send
4. ch send
5. ch close
6. var r1 = ch receive
7. var r2 = ch receive
8. var r3 = ch receive
   - Expected: r1 equals `1`
   - Expected: r2 equals `2`
   - Expected: r3 equals `3`
   - Expected: ch.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel(buffer: [], closed: false, count: 0)
ch.send(1)
ch.send(2)
ch.send(3)
ch.close()

# Can still receive even after close
var r1 = ch.receive()
var r2 = ch.receive()
var r3 = ch.receive()
expect(r1).to_equal(1)
expect(r2).to_equal(2)
expect(r3).to_equal(3)
expect(ch.is_empty()).to_equal(true)
```

</details>

### Full Pipeline Simulation

#### should run a complete pipeline with promises, futures, channel, and combinator

1. var ch = Channel
2. var p1 = Promise
3. p1 resolve
4. ch send
5. var p2 = Promise
6. p2 resolve
7. ch send
8. var p3 = Promise
9. p3 resolve
10. ch send
11. var f1 = future ready
12. var f2 = future ready
13. var f3 = future ready
   - Expected: ch.is_empty() is true
14. var joined = join all futures
   - Expected: joined.is_ready() is true
15. var final vals = joined value
   - Expected: final_vals[0] equals `100`
   - Expected: final_vals[1] equals `200`
   - Expected: final_vals[2] equals `300`
   - Expected: total equals `600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ch = Channel(buffer: [], closed: false, count: 0)

# Simulate 3 async tasks resolving promises and sending to channel
var p1 = Promise(state: PromiseState.Pending)
p1.resolve(100)
ch.send(p1.value())

var p2 = Promise(state: PromiseState.Pending)
p2.resolve(200)
ch.send(p2.value())

var p3 = Promise(state: PromiseState.Pending)
p3.resolve(300)
ch.send(p3.value())

# Collect channel results into futures
var f1 = future_ready(ch.receive())
var f2 = future_ready(ch.receive())
var f3 = future_ready(ch.receive())

expect(ch.is_empty()).to_equal(true)

# Join all futures
var joined = join_all_futures([f1, f2, f3])
expect(joined.is_ready()).to_equal(true)
var final_vals = joined.value()
expect(final_vals[0]).to_equal(100)
expect(final_vals[1]).to_equal(200)
expect(final_vals[2]).to_equal(300)

# Verify total sum
var total = 0
for v in final_vals:
    total = total + v
expect(total).to_equal(600)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)
- **Plan:** [doc/03_plan/async_promise_intensive_tests.md](doc/03_plan/async_promise_intensive_tests.md)
- **Design:** [doc/05_design/async_promise_intensive_tests.md](doc/05_design/async_promise_intensive_tests.md)


</details>
