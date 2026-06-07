# Async Combinators Intensive Tests

> Intensive tests for future combinators: join_all, select, race, timeout, zip, and retry patterns.

<!-- sdn-diagram:id=combinators_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=combinators_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

combinators_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=combinators_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Combinators Intensive Tests

Intensive tests for future combinators: join_all, select, race, timeout, zip, and retry patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | doc/requirement/async_promise_intensive_tests.md |
| Source | `test/01_unit/lib/nogc_async_mut/combinators_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Intensive tests for future combinators: join_all, select, race, timeout,
zip, and retry patterns.

## Scenarios

### Async Combinators Intensive

### join_all

#### returns ready with all values when all futures are ready

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture ready
3. var f3 = SimpleFuture ready
4. var result = join all
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `[10, 20, 30]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(10)
var f2 = SimpleFuture.ready(20)
var f3 = SimpleFuture.ready(30)
var result = join_all([f1, f2, f3])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal([10, 20, 30])
```

</details>

#### returns pending when one future is pending

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture pending
3. var f3 = SimpleFuture ready
4. var result = join all
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(1)
var f2 = SimpleFuture.pending()
var f3 = SimpleFuture.ready(3)
var result = join_all([f1, f2, f3])
expect(result.is_pending()).to_equal(true)
```

</details>

#### returns failed when one future has failed

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture failed
3. var f3 = SimpleFuture ready
4. var result = join all
   - Expected: result.is_failed() is true
   - Expected: result.get_error() equals `oops`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(1)
var f2 = SimpleFuture.failed("oops")
var f3 = SimpleFuture.ready(3)
var result = join_all([f1, f2, f3])
expect(result.is_failed()).to_equal(true)
expect(result.get_error()).to_equal("oops")
```

</details>

#### returns ready with empty list for empty input

1. var result = join all
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = join_all([])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal([])
```

</details>

#### handles single item list

1. var result = join all
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `[42]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = join_all([SimpleFuture.ready(42)])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal([42])
```

</details>

#### preserves value order

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture ready
3. var f3 = SimpleFuture ready
4. var result = join all
5. var vals = result get value
   - Expected: vals[0] equals `a`
   - Expected: vals[1] equals `b`
   - Expected: vals[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready("a")
var f2 = SimpleFuture.ready("b")
var f3 = SimpleFuture.ready("c")
var result = join_all([f1, f2, f3])
var vals = result.get_value()
expect(vals[0]).to_equal("a")
expect(vals[1]).to_equal("b")
expect(vals[2]).to_equal("c")
```

</details>

### select_first

#### returns first ready future found

1. var f1 = SimpleFuture pending
2. var f2 = SimpleFuture ready
3. var f3 = SimpleFuture ready
4. var result = select first
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.pending()
var f2 = SimpleFuture.ready(99)
var f3 = SimpleFuture.ready(100)
var result = select_first([f1, f2, f3])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(99)
```

</details>

#### returns pending when all are pending

1. var f1 = SimpleFuture pending
2. var f2 = SimpleFuture pending
3. var result = select first
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.pending()
var f2 = SimpleFuture.pending()
var result = select_first([f1, f2])
expect(result.is_pending()).to_equal(true)
```

</details>

#### skips failed futures and finds ready

1. var f1 = SimpleFuture failed
2. var f2 = SimpleFuture pending
3. var f3 = SimpleFuture ready
4. var result = select first
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.failed("err")
var f2 = SimpleFuture.pending()
var f3 = SimpleFuture.ready(7)
var result = select_first([f1, f2, f3])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(7)
```

</details>

### race

#### returns first non-pending future

1. var f1 = SimpleFuture pending
2. var f2 = SimpleFuture ready
3. var f3 = SimpleFuture pending
4. var result = race
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.pending()
var f2 = SimpleFuture.ready(55)
var f3 = SimpleFuture.pending()
var result = race([f1, f2, f3])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(55)
```

</details>

#### returns pending when all are pending

1. var f1 = SimpleFuture pending
2. var f2 = SimpleFuture pending
3. var result = race
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.pending()
var f2 = SimpleFuture.pending()
var result = race([f1, f2])
expect(result.is_pending()).to_equal(true)
```

</details>

#### returns failed if first non-pending is failed

1. var f1 = SimpleFuture pending
2. var f2 = SimpleFuture failed
3. var f3 = SimpleFuture ready
4. var result = race
   - Expected: result.is_failed() is true
   - Expected: result.get_error() equals `race-fail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.pending()
var f2 = SimpleFuture.failed("race-fail")
var f3 = SimpleFuture.ready(1)
var result = race([f1, f2, f3])
expect(result.is_failed()).to_equal(true)
expect(result.get_error()).to_equal("race-fail")
```

</details>

#### returns ready if first non-pending is ready

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture failed
3. var result = race
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(200)
var f2 = SimpleFuture.failed("no")
var result = race([f1, f2])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(200)
```

</details>

### timeout_future

#### passes through when not timed out

1. var f = SimpleFuture ready
2. var result = timeout future
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SimpleFuture.ready(5)
var result = timeout_future(f, false)
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(5)
```

</details>

#### fails pending future when timed out

1. var f = SimpleFuture pending
2. var result = timeout future
   - Expected: result.is_failed() is true
   - Expected: result.get_error() equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SimpleFuture.pending()
var result = timeout_future(f, true)
expect(result.is_failed()).to_equal(true)
expect(result.get_error()).to_equal("timeout")
```

</details>

#### passes through ready future even when timed out

1. var f = SimpleFuture ready
2. var result = timeout future
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SimpleFuture.ready(42)
var result = timeout_future(f, true)
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(42)
```

</details>

### zip

#### returns paired values when both ready

1. var a = SimpleFuture ready
2. var b = SimpleFuture ready
3. var result = zip
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `["x", "y"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = SimpleFuture.ready("x")
var b = SimpleFuture.ready("y")
var result = zip(a, b)
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(["x", "y"])
```

</details>

#### returns pending when one is pending

1. var a = SimpleFuture ready
2. var b = SimpleFuture pending
3. var result = zip
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = SimpleFuture.ready(1)
var b = SimpleFuture.pending()
var result = zip(a, b)
expect(result.is_pending()).to_equal(true)
```

</details>

#### returns failed when one is failed

1. var a = SimpleFuture failed
2. var b = SimpleFuture ready
3. var result = zip
   - Expected: result.is_failed() is true
   - Expected: result.get_error() equals `zip-err`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = SimpleFuture.failed("zip-err")
var b = SimpleFuture.ready(2)
var result = zip(a, b)
expect(result.is_failed()).to_equal(true)
expect(result.get_error()).to_equal("zip-err")
```

</details>

#### returns pending when both are pending

1. var a = SimpleFuture pending
2. var b = SimpleFuture pending
3. var result = zip
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = SimpleFuture.pending()
var b = SimpleFuture.pending()
var result = zip(a, b)
expect(result.is_pending()).to_equal(true)
```

</details>

### retry

#### succeeds on first try

1. var make = \: SimpleFuture ready
2. var result = retry
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var make = \: SimpleFuture.ready(1)
var result = retry(make, 3)
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(1)
```

</details>

#### succeeds after retries

1. var make = \: SimpleFuture ready
2. var result = retry
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Cannot use mutable closure capture, so test with always-ready
var make = \: SimpleFuture.ready("done")
var result = retry(make, 5)
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal("done")
```

</details>

#### fails when all retries exhausted

1. var make = \: SimpleFuture failed
2. var result = retry
   - Expected: result.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var make = \: SimpleFuture.failed("always fails")
var result = retry(make, 2)
expect(result.is_failed()).to_equal(true)
```

</details>

#### fails immediately with zero retries if not ready

1. var make = \: SimpleFuture failed
2. var result = retry
   - Expected: result.is_failed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var make = \: SimpleFuture.failed("nope")
var result = retry(make, 0)
expect(result.is_failed()).to_equal(true)
```

</details>

### all_settled

#### returns ready when all futures are ready

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture ready
3. var result = all settled
   - Expected: result.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(1)
var f2 = SimpleFuture.ready(2)
var result = all_settled([f1, f2])
expect(result.is_ready()).to_equal(true)
```

</details>

#### returns ready when all futures are failed

1. var f1 = SimpleFuture failed
2. var f2 = SimpleFuture failed
3. var result = all settled
   - Expected: result.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.failed("a")
var f2 = SimpleFuture.failed("b")
var result = all_settled([f1, f2])
expect(result.is_ready()).to_equal(true)
```

</details>

#### returns ready for mixed ready and failed

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture failed
3. var result = all settled
   - Expected: result.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(1)
var f2 = SimpleFuture.failed("err")
var result = all_settled([f1, f2])
expect(result.is_ready()).to_equal(true)
```

</details>

#### returns pending when some are still pending

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture pending
3. var result = all settled
   - Expected: result.is_pending() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(1)
var f2 = SimpleFuture.pending()
var result = all_settled([f1, f2])
expect(result.is_pending()).to_equal(true)
```

</details>

### first_ok

#### returns first ready future

1. var f1 = SimpleFuture ready
2. var f2 = SimpleFuture ready
3. var result = first ok
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.ready(10)
var f2 = SimpleFuture.ready(20)
var result = first_ok([f1, f2])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(10)
```

</details>

#### skips failed futures and returns first ready

1. var f1 = SimpleFuture failed
2. var f2 = SimpleFuture failed
3. var f3 = SimpleFuture ready
4. var result = first ok
   - Expected: result.is_ready() is true
   - Expected: result.get_value() equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.failed("bad")
var f2 = SimpleFuture.failed("worse")
var f3 = SimpleFuture.ready(77)
var result = first_ok([f1, f2, f3])
expect(result.is_ready()).to_equal(true)
expect(result.get_value()).to_equal(77)
```

</details>

#### returns failed when all futures have failed

1. var f1 = SimpleFuture failed
2. var f2 = SimpleFuture failed
3. var result = first ok
   - Expected: result.is_failed() is true
   - Expected: result.get_error() equals `e2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f1 = SimpleFuture.failed("e1")
var f2 = SimpleFuture.failed("e2")
var result = first_ok([f1, f2])
expect(result.is_failed()).to_equal(true)
expect(result.get_error()).to_equal("e2")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/async_promise_intensive_tests.md](doc/requirement/async_promise_intensive_tests.md)


</details>
