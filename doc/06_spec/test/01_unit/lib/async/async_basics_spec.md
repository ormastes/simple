# async_basics_spec

> Async Basics Unit Tests

<!-- sdn-diagram:id=async_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_basics_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_basics_spec

Async Basics Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-ASYNC-001 |
| Category | Lib \| Async |
| Status | Implemented |
| Source | `test/01_unit/lib/async/async_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Async Basics Unit Tests

Behavioral tests for Future, Poll, Runtime, gather, race, and AsyncIO.
Interpreter quirks:
  - Chained enum method calls fail; always use intermediate vars.
  - Future.is_ready() chains self.poll().is_ready() internally and fails;
    use f.poll() -> var -> is_ready() on Poll directly.
  - return inside it blocks not supported; avoided in all test bodies.

## Scenarios

### Poll enum

#### Poll.Ready carries its value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p: Poll<i64> = Poll.Ready(42)
val got = p.unwrap()
expect(got).to_equal(42)
```

</details>

#### Poll.Ready is_ready returns true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p: Poll<i64> = Poll.Ready(7)
val ready = p.is_ready()
assert_true(ready)
```

</details>

#### Poll.Pending is_ready returns false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p: Poll<i64> = Poll.Pending
val ready = p.is_ready()
assert_false(ready)
```

</details>

#### Poll.Pending is_pending returns true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p: Poll<i64> = Poll.Pending
val pending = p.is_pending()
assert_true(pending)
```

</details>

#### Poll.Ready is_pending returns false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p: Poll<i64> = Poll.Ready(1)
val pending = p.is_pending()
assert_false(pending)
```

</details>

### Future construction

#### from_value poll returns Poll.Ready

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(42)
val result = f.poll()
val is_rdy = result.is_ready()
assert_true(is_rdy)
```

</details>

#### pending poll returns Poll.Pending

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.pending<i64>()
val result = f.poll()
val is_pend = result.is_pending()
assert_true(is_pend)
```

</details>

#### from_value poll unwrap returns the value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(123)
val result = f.poll()
val value = result.unwrap()
expect(value).to_equal(123)
```

</details>

#### pending poll unwrap-ready is false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.pending<i64>()
val result = f.poll()
val is_rdy = result.is_ready()
assert_false(is_rdy)
```

</details>

### Future map

#### map over ready future transforms value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(10)
val mapped = f.map(\v: v * 2)
val result = mapped.poll()
val value = result.unwrap()
expect(value).to_equal(20)
```

</details>

#### map over pending future poll is pending

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.pending<i64>()
val mapped = f.map(\v: v + 1)
val result = mapped.poll()
val is_pend = result.is_pending()
assert_true(is_pend)
```

</details>

### Future then

#### then over ready future chains correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.from_value(5)
val chained = f.then(\v: Future.from_value(v + 100))
val result = chained.poll()
val value = result.unwrap()
expect(value).to_equal(105)
```

</details>

#### then over pending future poll is pending

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = Future.pending<i64>()
val chained = f.then(\v: Future.from_value(v))
val result = chained.poll()
val is_pend = result.is_pending()
assert_true(is_pend)
```

</details>

### Runtime run_once

#### run_once returns false on empty runtime

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rt = Runtime.new()
val still_going = rt.run_once()
assert_false(still_going)
```

</details>

#### run_once completes a ready task

- rt run once
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rt = Runtime.new()
val task_id = rt.spawn(Future.from_value(()))
rt.run_once()
val done = rt.completed.has(task_id)
assert_true(done)
```

</details>

#### run_once does not complete a pending task

- rt run once
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rt = Runtime.new()
val task_id = rt.spawn(Future.pending<()>())
rt.run_once()
val in_completed = rt.completed.has(task_id)
assert_false(in_completed)
```

</details>

#### block_on completes for immediately-ready future

- rt block on
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rt = Runtime.new()
rt.block_on(Future.from_value(()))
# Reaching here without hanging means block_on returned
assert_true(true)
```

</details>

### gather combinator

#### gather over all-ready futures poll is ready

- Future from value
- Future from value
- Future from value
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures: [Future<i64>] = [
    Future.from_value(1),
    Future.from_value(2),
    Future.from_value(3)
]
val result = gather(futures)
val polled = result.poll()
val is_rdy = polled.is_ready()
assert_true(is_rdy)
```

</details>

#### gather over all-ready futures collects correct count

- Future from value
- Future from value
   - Expected: values.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures: [Future<i64>] = [
    Future.from_value(10),
    Future.from_value(20)
]
val result = gather(futures)
val polled = result.poll()
val values = polled.unwrap()
expect(values.len()).to_equal(2)
```

</details>

#### gather with any pending future poll is pending

- Future from value
- Future pending<i64>
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures: [Future<i64>] = [
    Future.from_value(1),
    Future.pending<i64>()
]
val result = gather(futures)
val polled = result.poll()
val is_pend = polled.is_pending()
assert_true(is_pend)
```

</details>

### race combinator

#### race returns first ready future value

- Future from value
- Future from value
   - Expected: value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures: [Future<i64>] = [
    Future.from_value(42),
    Future.from_value(99)
]
val result = race(futures)
val polled = result.poll()
val value = polled.unwrap()
expect(value).to_equal(42)
```

</details>

#### race over all-pending poll is pending

- Future pending<i64>
- Future pending<i64>
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures: [Future<i64>] = [
    Future.pending<i64>(),
    Future.pending<i64>()
]
val result = race(futures)
val polled = result.poll()
val is_pend = polled.is_pending()
assert_true(is_pend)
```

</details>

#### race skips pending and finds ready

- Future pending<i64>
- Future from value
   - Expected: value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val futures: [Future<i64>] = [
    Future.pending<i64>(),
    Future.from_value(7)
]
val result = race(futures)
val polled = result.poll()
val value = polled.unwrap()
expect(value).to_equal(7)
```

</details>

### AsyncIO yield_now and sleep

#### yield_now poll is pending

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val io = AsyncIO.new()
val f = io.yield_now()
val polled = f.poll()
val is_pend = polled.is_pending()
assert_true(is_pend)
```

</details>

#### sleep poll is pending

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val io = AsyncIO.new()
val f = io.sleep(100)
val polled = f.poll()
val is_pend = polled.is_pending()
assert_true(is_pend)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
