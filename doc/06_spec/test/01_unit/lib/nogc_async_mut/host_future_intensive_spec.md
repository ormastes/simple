# HostFuture & HostPromise Intensive Tests

> Intensive tests for HostFuture operations (poll, map, then, catch, timeout, cancel, delay) and HostPromise (complete, fail, double-complete prevention).

<!-- sdn-diagram:id=host_future_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_future_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_future_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_future_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HostFuture & HostPromise Intensive Tests

Intensive tests for HostFuture operations (poll, map, then, catch, timeout, cancel, delay) and HostPromise (complete, fail, double-complete prevention).

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
| Source | `test/01_unit/lib/nogc_async_mut/host_future_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Intensive tests for HostFuture operations (poll, map, then, catch, timeout,
cancel, delay) and HostPromise (complete, fail, double-complete prevention).

## Scenarios

### HostFuture & HostPromise Intensive

### HostFuture Creation

#### creates a ready future with a value

1. var fut = HostFuture ready
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(42)
expect(fut.is_ready()).to_equal(true)
```

</details>

#### creates a ready future and stores the correct value

1. var fut = HostFuture ready
2. var p = fut poll
   - Expected: p.unwrap() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready("hello")
var p = fut.poll()
expect(p.unwrap()).to_equal("hello")
```

</details>

#### creates a pending future

1. var fut = HostFuture pending
   - Expected: fut.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
expect(fut.is_pending()).to_equal(true)
```

</details>

#### creates a failed future

1. var fut = HostFuture failed
   - Expected: fut.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.failed("oops")
expect(fut.is_failed()).to_equal(true)
```

</details>

#### ready future is not pending

1. var fut = HostFuture ready
   - Expected: fut.is_pending() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(1)
expect(fut.is_pending()).to_equal(false)
```

</details>

#### ready future is not failed

1. var fut = HostFuture ready
   - Expected: fut.is_failed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(1)
expect(fut.is_failed()).to_equal(false)
```

</details>

#### pending future is not ready

1. var fut = HostFuture pending
   - Expected: fut.is_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
expect(fut.is_ready()).to_equal(false)
```

</details>

#### failed future is not ready

1. var fut = HostFuture failed
   - Expected: fut.is_ready() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.failed("err")
expect(fut.is_ready()).to_equal(false)
```

</details>

### HostFuture Polling

#### poll on ready future returns Poll.Ready

1. var fut = HostFuture ready
2. var p = fut poll
   - Expected: p.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(10)
var p = fut.poll()
expect(p.is_ready()).to_equal(true)
```

</details>

#### poll on ready future unwraps to correct value

1. var fut = HostFuture ready
2. var p = fut poll
   - Expected: p.unwrap() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(99)
var p = fut.poll()
expect(p.unwrap()).to_equal(99)
```

</details>

#### poll on pending future returns Poll.Pending

1. var fut = HostFuture pending
2. var p = fut poll
   - Expected: p.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
var p = fut.poll()
expect(p.is_pending()).to_equal(true)
```

</details>

#### poll on failed future returns Poll.Ready wrapping the error state

1. var fut = HostFuture failed
2. var p = fut poll
   - Expected: p.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.failed("timeout")
var p = fut.poll()
expect(p.is_ready()).to_equal(true)
```

</details>

### HostFuture Map

#### map applies function to ready value

1. var fut = HostFuture ready
2. var mapped = fut map
3. var p = mapped poll
   - Expected: p.unwrap() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(5)
var mapped = fut.map(_1 * 2)
var p = mapped.poll()
expect(p.unwrap()).to_equal(10)
```

</details>

#### map on pending returns pending

1. var fut = HostFuture pending
2. var mapped = fut map
   - Expected: mapped.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
var mapped = fut.map(_1 + 1)
expect(mapped.is_pending()).to_equal(true)
```

</details>

#### map on failed propagates error

1. var fut = HostFuture failed
2. var mapped = fut map
   - Expected: mapped.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.failed("bad")
var mapped = fut.map(_1 + 1)
expect(mapped.is_failed()).to_equal(true)
```

</details>

#### map chain applies functions in sequence

1. var fut = HostFuture ready
2. var step1 = fut map
3. var step2 = step1 map
4. var p = step2 poll
   - Expected: p.unwrap() equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(2)
var step1 = fut.map(_1 + 3)
var step2 = step1.map(_1 * 10)
var p = step2.poll()
expect(p.unwrap()).to_equal(50)
```

</details>

#### map with identity returns same value

1. var fut = HostFuture ready
2. var mapped = fut map
3. var p = mapped poll
   - Expected: p.unwrap() equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready("abc")
var mapped = fut.map(_1)
var p = mapped.poll()
expect(p.unwrap()).to_equal("abc")
```

</details>

### HostFuture Then

#### then on ready with ready-returning function

1. var fut = HostFuture ready
2. var result = fut then
3. var p = result poll
   - Expected: p.unwrap() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(3)
var result = fut.then(HostFuture.ready(_1 * 3))
var p = result.poll()
expect(p.unwrap()).to_equal(9)
```

</details>

#### then on ready with pending-returning function

1. var fut = HostFuture ready
2. var result = fut then
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(3)
var result = fut.then(\_: HostFuture.pending())
expect(result.is_pending()).to_equal(true)
```

</details>

#### then on pending returns pending regardless

1. var fut = HostFuture pending
2. var result = fut then
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
var result = fut.then(HostFuture.ready(_1))
expect(result.is_pending()).to_equal(true)
```

</details>

#### then on failed propagates failure

1. var fut = HostFuture failed
2. var result = fut then
   - Expected: result.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.failed("err")
var result = fut.then(HostFuture.ready(_1))
expect(result.is_failed()).to_equal(true)
```

</details>

#### then chaining multiple futures

1. var fut = HostFuture ready
2. var step1 = fut then
3. var step2 = step1 then
4. var p = step2 poll
   - Expected: p.unwrap() equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(1)
var step1 = fut.then(HostFuture.ready(_1 + 10))
var step2 = step1.then(HostFuture.ready(_1 + 100))
var p = step2.poll()
expect(p.unwrap()).to_equal(111)
```

</details>

### HostFuture Error Handling

#### catch_err on failed future recovers

1. var fut = HostFuture failed
2. var recovered = fut catch err
   - Expected: recovered.is_ready() is true
3. var p = recovered poll
   - Expected: p.unwrap() equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.failed("network_error")
var recovered = fut.catch_err(\_: HostFuture.ready("default"))
expect(recovered.is_ready()).to_equal(true)
var p = recovered.poll()
expect(p.unwrap()).to_equal("default")
```

</details>

#### catch_err on ready future passes through

1. var fut = HostFuture ready
2. var same = fut catch err
   - Expected: same.is_ready() is true
3. var p = same poll
   - Expected: p.unwrap() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(42)
var same = fut.catch_err(\_: HostFuture.ready(0))
expect(same.is_ready()).to_equal(true)
var p = same.poll()
expect(p.unwrap()).to_equal(42)
```

</details>

#### catch_err on pending future passes through

1. var fut = HostFuture pending
2. var same = fut catch err
   - Expected: same.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
var same = fut.catch_err(\_: HostFuture.ready(0))
expect(same.is_pending()).to_equal(true)
```

</details>

#### error then catch then map recovery chain

1. var fut = HostFuture failed
2. var recovered = fut catch err
3. var mapped = recovered map
4. var p = mapped poll
   - Expected: p.unwrap() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.failed("broken")
var recovered = fut.catch_err(\_: HostFuture.ready(0))
var mapped = recovered.map(_1 + 100)
var p = mapped.poll()
expect(p.unwrap()).to_equal(100)
```

</details>

### HostFuture Timeout

#### with_timeout sets deadline on future

1. var fut = HostFuture pending
2. fut with timeout
   - Expected: fut.deadline equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
fut.with_timeout(millis: 5000)
expect(fut.deadline).to_equal(5000)
```

</details>

#### with_timeout on ready future still sets deadline

1. var fut = HostFuture ready
2. fut with timeout
   - Expected: fut.deadline equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(1)
fut.with_timeout(millis: 3000)
expect(fut.deadline).to_equal(3000)
```

</details>

#### default deadline is zero

1. var fut = HostFuture pending
   - Expected: fut.deadline equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
expect(fut.deadline).to_equal(0)
```

</details>

### HostFuture Cancel

#### cancel sets pending future to failed with cancelled

1. var fut = HostFuture pending
2. fut cancel
   - Expected: fut.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
fut.cancel()
expect(fut.is_failed()).to_equal(true)
```

</details>

#### cancel on ready future sets it to failed

1. var fut = HostFuture ready
2. fut cancel
   - Expected: fut.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.ready(10)
fut.cancel()
expect(fut.is_failed()).to_equal(true)
```

</details>

#### cancelled future is no longer pending

1. var fut = HostFuture pending
2. fut cancel
   - Expected: fut.is_pending() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
fut.cancel()
expect(fut.is_pending()).to_equal(false)
```

</details>

### HostPromise Basics

#### creates a future-promise pair

1. var pair = HostPromise new
   - Expected: fut.is_pending() is true
   - Expected: promise.is_completed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var fut = pair[0]
var promise = pair[1]
expect(fut.is_pending()).to_equal(true)
expect(promise.is_completed()).to_equal(false)
```

</details>

#### complete resolves the future

1. var pair = HostPromise new
2. var ok = promise complete
   - Expected: ok is true
   - Expected: promise.future.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
var ok = promise.complete(42)
expect(ok).to_equal(true)
expect(promise.future.is_ready()).to_equal(true)
```

</details>

#### complete sets the correct value in the future

1. var pair = HostPromise new
2. promise complete
3. var p = promise future poll
   - Expected: p.unwrap() equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.complete("done")
var p = promise.future.poll()
expect(p.unwrap()).to_equal("done")
```

</details>

#### fail sets the future to failed state

1. var pair = HostPromise new
2. var ok = promise fail
   - Expected: ok is true
   - Expected: promise.future.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
var ok = promise.fail("error_msg")
expect(ok).to_equal(true)
expect(promise.future.is_failed()).to_equal(true)
```

</details>

#### is_completed returns true after complete

1. var pair = HostPromise new
2. promise complete
   - Expected: promise.is_completed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.complete(1)
expect(promise.is_completed()).to_equal(true)
```

</details>

#### is_completed returns true after fail

1. var pair = HostPromise new
2. promise fail
   - Expected: promise.is_completed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.fail("x")
expect(promise.is_completed()).to_equal(true)
```

</details>

### HostPromise Double Complete

#### second complete returns false

1. var pair = HostPromise new
2. promise complete
3. var second = promise complete
   - Expected: second is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.complete(1)
var second = promise.complete(2)
expect(second).to_equal(false)
```

</details>

#### second fail returns false

1. var pair = HostPromise new
2. promise fail
3. var second = promise fail
   - Expected: second is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.fail("first")
var second = promise.fail("second")
expect(second).to_equal(false)
```

</details>

#### complete then fail returns false for fail

1. var pair = HostPromise new
2. promise complete
3. var fail ok = promise fail
   - Expected: fail_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.complete(1)
var fail_ok = promise.fail("err")
expect(fail_ok).to_equal(false)
```

</details>

#### fail then complete returns false for complete

1. var pair = HostPromise new
2. promise fail
3. var complete ok = promise complete
   - Expected: complete_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.fail("err")
var complete_ok = promise.complete(1)
expect(complete_ok).to_equal(false)
```

</details>

#### original value preserved after double complete

1. var pair = HostPromise new
2. promise complete
3. promise complete
4. var p = promise future poll
   - Expected: p.unwrap() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pair = HostPromise.new()
var promise = pair[1]
promise.complete(100)
promise.complete(200)
var p = promise.future.poll()
expect(p.unwrap()).to_equal(100)
```

</details>

### HostFuture State Transitions

#### pending to ready via complete

1. var fut = HostFuture pending
   - Expected: fut.is_pending() is true
2. fut complete
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
expect(fut.is_pending()).to_equal(true)
fut.complete(7)
expect(fut.is_ready()).to_equal(true)
```

</details>

#### pending to failed via fail

1. var fut = HostFuture pending
   - Expected: fut.is_pending() is true
2. fut fail
   - Expected: fut.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
expect(fut.is_pending()).to_equal(true)
fut.fail("went_wrong")
expect(fut.is_failed()).to_equal(true)
```

</details>

#### complete overwrites state to ready

1. var fut = HostFuture pending
2. fut complete
   - Expected: fut.is_pending() is false
   - Expected: fut.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
fut.complete("value")
expect(fut.is_pending()).to_equal(false)
expect(fut.is_ready()).to_equal(true)
```

</details>

#### fail overwrites state to failed

1. var fut = HostFuture pending
2. fut fail
   - Expected: fut.is_pending() is false
   - Expected: fut.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fut = HostFuture.pending()
fut.fail("err")
expect(fut.is_pending()).to_equal(false)
expect(fut.is_failed()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)
- **Plan:** [doc/03_plan/async_promise_intensive_tests.md](doc/03_plan/async_promise_intensive_tests.md)
- **Design:** [doc/05_design/async_promise_intensive_tests.md](doc/05_design/async_promise_intensive_tests.md)


</details>
