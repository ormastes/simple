# Work-Stealing, Waker & Collections Intensive Tests

> Intensive tests for WorkStealingQueue (LIFO pop, FIFO steal), Waker notification system, JoinSet dynamic task collection, and FuturesUnordered.

<!-- sdn-diagram:id=work_stealing_waker_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=work_stealing_waker_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

work_stealing_waker_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=work_stealing_waker_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Work-Stealing, Waker & Collections Intensive Tests

Intensive tests for WorkStealingQueue (LIFO pop, FIFO steal), Waker notification system, JoinSet dynamic task collection, and FuturesUnordered.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | doc/requirement/async_promise_intensive_tests.md |
| Source | `test/01_unit/lib/nogc_async_mut/work_stealing_waker_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Intensive tests for WorkStealingQueue (LIFO pop, FIFO steal), Waker notification
system, JoinSet dynamic task collection, and FuturesUnordered.

## Scenarios

### WorkStealingQueue Basics

#### new queue is empty

1. var q = WorkStealingQueue new
   - Expected: q.is_empty() is true
   - Expected: q.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
expect(q.is_empty()).to_equal(true)
expect(q.len()).to_equal(0)
```

</details>

#### push increases length

1. var q = WorkStealingQueue new
2. q push
   - Expected: q.len() equals `1`
   - Expected: q.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(10)
expect(q.len()).to_equal(1)
expect(q.is_empty()).to_equal(false)
```

</details>

#### single push and pop returns the item

1. var q = WorkStealingQueue new
2. q push
   - Expected: result equals `42`
   - Expected: q.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(42)
val result = q.pop()
expect(result).to_equal(42)
expect(q.is_empty()).to_equal(true)
```

</details>

### WorkStealingQueue LIFO Pop

#### pop returns items in LIFO order

1. var q = WorkStealingQueue new
2. q push
3. q push
4. q push
   - Expected: q.pop() equals `3`
   - Expected: q.pop() equals `2`
   - Expected: q.pop() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(1)
q.push(2)
q.push(3)
expect(q.pop()).to_equal(3)
expect(q.pop()).to_equal(2)
expect(q.pop()).to_equal(1)
```

</details>

#### queue is empty after popping all items

1. var q = WorkStealingQueue new
2. q push
3. q push
4. q pop
5. q pop
   - Expected: q.is_empty() is true
   - Expected: q.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(10)
q.push(20)
q.pop()
q.pop()
expect(q.is_empty()).to_equal(true)
expect(q.len()).to_equal(0)
```

</details>

### WorkStealingQueue FIFO Steal

#### steal returns items in FIFO order

1. var q = WorkStealingQueue new
2. q push
3. q push
4. q push
   - Expected: q.steal() equals `1`
   - Expected: q.steal() equals `2`
   - Expected: q.steal() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(1)
q.push(2)
q.push(3)
expect(q.steal()).to_equal(1)
expect(q.steal()).to_equal(2)
expect(q.steal()).to_equal(3)
```

</details>

#### queue is empty after stealing all items

1. var q = WorkStealingQueue new
2. q push
3. q push
4. q steal
5. q steal
   - Expected: q.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(5)
q.push(6)
q.steal()
q.steal()
expect(q.is_empty()).to_equal(true)
```

</details>

### WorkStealingQueue Mixed Pop and Steal

#### pop and steal interleaved produce correct results

1. var q = WorkStealingQueue new
2. q push
3. q push
4. q push
5. q push
   - Expected: q.steal() equals `1`
   - Expected: q.pop() equals `4`
   - Expected: q.steal() equals `2`
   - Expected: q.pop() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(1)
q.push(2)
q.push(3)
q.push(4)
# steal takes from front (FIFO), pop takes from back (LIFO)
expect(q.steal()).to_equal(1)
expect(q.pop()).to_equal(4)
expect(q.steal()).to_equal(2)
expect(q.pop()).to_equal(3)
```

</details>

#### queue is empty after fully draining via mixed ops

1. var q = WorkStealingQueue new
2. q push
3. q push
4. q steal
5. q pop
   - Expected: q.is_empty() is true
   - Expected: q.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
q.push(10)
q.push(20)
q.steal()
q.pop()
expect(q.is_empty()).to_equal(true)
expect(q.len()).to_equal(0)
```

</details>

### WorkStealingQueue Edge Cases

#### pop on empty queue returns sentinel 0

1. var q = WorkStealingQueue new
   - Expected: q.pop() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
expect(q.pop()).to_equal(0)
```

</details>

#### steal on empty queue returns sentinel 0

1. var q = WorkStealingQueue new
   - Expected: q.steal() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = WorkStealingQueue.new()
expect(q.steal()).to_equal(0)
```

</details>

#### single item can be popped or stolen

1. var q1 = WorkStealingQueue new
2. q1 push
   - Expected: q1.pop() equals `99`
3. var q2 = WorkStealingQueue new
4. q2 push
   - Expected: q2.steal() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q1 = WorkStealingQueue.new()
q1.push(99)
expect(q1.pop()).to_equal(99)

var q2 = WorkStealingQueue.new()
q2.push(99)
expect(q2.steal()).to_equal(99)
```

</details>

### Waker Basics

#### new waker has zero wake count

1. var w = Waker new
   - Expected: w.wake_count equals `0`
   - Expected: w.task_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = Waker.new(task_id: 1)
expect(w.wake_count).to_equal(0)
expect(w.task_id).to_equal(1)
```

</details>

#### wake increments the count

1. var w = Waker new
2. w wake
   - Expected: w.wake_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = Waker.new(task_id: 1)
w.wake()
expect(w.wake_count).to_equal(1)
```

</details>

#### wake_by_ref also increments the count

1. var w = Waker new
2. w wake by ref
   - Expected: w.wake_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = Waker.new(task_id: 2)
w.wake_by_ref()
expect(w.wake_count).to_equal(1)
```

</details>

### Waker will_wake

#### returns true for same task_id

1. var w1 = Waker new
2. var w2 = Waker new
   - Expected: w1.will_wake(w2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w1 = Waker.new(task_id: 5)
var w2 = Waker.new(task_id: 5)
expect(w1.will_wake(w2)).to_equal(true)
```

</details>

#### returns false for different task_id

1. var w1 = Waker new
2. var w2 = Waker new
   - Expected: w1.will_wake(w2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w1 = Waker.new(task_id: 5)
var w2 = Waker.new(task_id: 6)
expect(w1.will_wake(w2)).to_equal(false)
```

</details>

### Waker Multiple Wakes

#### tracks cumulative wake count

1. var w = Waker new
2. w wake
3. w wake
4. w wake
5. w wake
6. w wake
   - Expected: w.wake_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = Waker.new(task_id: 10)
w.wake()
w.wake()
w.wake()
w.wake()
w.wake()
expect(w.wake_count).to_equal(5)
```

</details>

#### wake and wake_by_ref both contribute to count

1. var w = Waker new
2. w wake
3. w wake by ref
4. w wake
   - Expected: w.wake_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = Waker.new(task_id: 20)
w.wake()
w.wake_by_ref()
w.wake()
expect(w.wake_count).to_equal(3)
```

</details>

### Context

#### from_waker preserves the waker

1. var w = Waker new
2. var ctx = Context from waker
   - Expected: ctx.waker.task_id equals `7`
   - Expected: ctx.waker.wake_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = Waker.new(task_id: 7)
var ctx = Context.from_waker(waker: w)
expect(ctx.waker.task_id).to_equal(7)
expect(ctx.waker.wake_count).to_equal(0)
```

</details>

### JoinSet Basics

#### new JoinSet is empty

1. var js = JoinSet new
   - Expected: js.is_empty() is true
   - Expected: js.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
expect(js.is_empty()).to_equal(true)
expect(js.len()).to_equal(0)
```

</details>

#### add increases length

1. var js = JoinSet new
2. js add
   - Expected: js.len() equals `1`
   - Expected: js.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
js.add(SFuture.ready(1))
expect(js.len()).to_equal(1)
expect(js.is_empty()).to_equal(false)
```

</details>

#### add multiple tasks

1. var js = JoinSet new
2. js add
3. js add
4. js add
   - Expected: js.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
js.add(SFuture.ready(10))
js.add(SFuture.pending())
js.add(SFuture.ready(30))
expect(js.len()).to_equal(3)
```

</details>

### JoinSet join_next

#### returns ready value and removes it

1. var js = JoinSet new
2. js add
   - Expected: v equals `42`
   - Expected: js.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
js.add(SFuture.ready(42))
val v = js.join_next()
expect(v).to_equal(42)
expect(js.len()).to_equal(0)
```

</details>

#### returns 0 when no tasks are ready

1. var js = JoinSet new
2. js add
3. js add
   - Expected: js.join_next() equals `0`
   - Expected: js.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
js.add(SFuture.pending())
js.add(SFuture.pending())
expect(js.join_next()).to_equal(0)
expect(js.len()).to_equal(2)
```

</details>

#### skips pending and returns first ready

1. var js = JoinSet new
2. js add
3. js add
4. js add
   - Expected: v equals `77`
   - Expected: js.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
js.add(SFuture.pending())
js.add(SFuture.ready(77))
js.add(SFuture.pending())
val v = js.join_next()
expect(v).to_equal(77)
expect(js.len()).to_equal(2)
```

</details>

### JoinSet pending_count

#### counts only pending futures

1. var js = JoinSet new
2. js add
3. js add
4. js add
5. js add
   - Expected: js.pending_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
js.add(SFuture.ready(1))
js.add(SFuture.pending())
js.add(SFuture.ready(3))
js.add(SFuture.pending())
expect(js.pending_count()).to_equal(2)
```

</details>

#### returns 0 when all are ready

1. var js = JoinSet new
2. js add
3. js add
   - Expected: js.pending_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var js = JoinSet.new()
js.add(SFuture.ready(1))
js.add(SFuture.ready(2))
expect(js.pending_count()).to_equal(0)
```

</details>

### FuturesUnordered Basics

#### new FuturesUnordered is empty

1. var fu = FuturesUnordered new
   - Expected: fu.is_empty() is true
   - Expected: fu.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fu = FuturesUnordered.new()
expect(fu.is_empty()).to_equal(true)
expect(fu.len()).to_equal(0)
```

</details>

#### push adds futures

1. var fu = FuturesUnordered new
2. fu push
3. fu push
   - Expected: fu.len() equals `2`
   - Expected: fu.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fu = FuturesUnordered.new()
fu.push(SFuture.ready(10))
fu.push(SFuture.pending())
expect(fu.len()).to_equal(2)
expect(fu.is_empty()).to_equal(false)
```

</details>

### FuturesUnordered try_next

#### returns first ready value and removes it

1. var fu = FuturesUnordered new
2. fu push
   - Expected: v equals `55`
   - Expected: fu.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fu = FuturesUnordered.new()
fu.push(SFuture.ready(55))
val v = fu.try_next()
expect(v).to_equal(55)
expect(fu.len()).to_equal(0)
```

</details>

#### returns 0 when none are ready

1. var fu = FuturesUnordered new
2. fu push
   - Expected: fu.try_next() equals `0`
   - Expected: fu.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fu = FuturesUnordered.new()
fu.push(SFuture.pending())
expect(fu.try_next()).to_equal(0)
expect(fu.len()).to_equal(1)
```

</details>

#### skips pending and returns first ready

1. var fu = FuturesUnordered new
2. fu push
3. fu push
4. fu push
   - Expected: v equals `88`
   - Expected: fu.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fu = FuturesUnordered.new()
fu.push(SFuture.pending())
fu.push(SFuture.pending())
fu.push(SFuture.ready(88))
val v = fu.try_next()
expect(v).to_equal(88)
expect(fu.len()).to_equal(2)
```

</details>

#### drains all ready futures one by one

1. var fu = FuturesUnordered new
2. fu push
3. fu push
4. fu push
   - Expected: v1 equals `1`
   - Expected: v2 equals `2`
   - Expected: v3 equals `3`
   - Expected: fu.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fu = FuturesUnordered.new()
fu.push(SFuture.ready(1))
fu.push(SFuture.ready(2))
fu.push(SFuture.ready(3))
val v1 = fu.try_next()
val v2 = fu.try_next()
val v3 = fu.try_next()
expect(v1).to_equal(1)
expect(v2).to_equal(2)
expect(v3).to_equal(3)
expect(fu.is_empty()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)


</details>
