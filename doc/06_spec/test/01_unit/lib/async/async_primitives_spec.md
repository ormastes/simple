# async_primitives_spec

> Async Primitives Unit Tests

<!-- sdn-diagram:id=async_primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_primitives_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_primitives_spec

Async Primitives Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-ASYNC-PRIM-001 |
| Category | Lib \| Async |
| Status | Implemented |
| Source | `test/01_unit/lib/async/async_primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Async Primitives Unit Tests

Behavioral tests for CancellationToken, AsyncMutex, AsyncSemaphore,
TimerFuture, and timeout_with_deadline.

Interpreter quirks observed in async_basics_spec:
  - Chained enum method calls fail; always use intermediate vars.
  - return inside it blocks not supported; avoided in all test bodies.
  - no bare expect(cond); no expect(a==b).to_equal(true)
  - no named-arg fn calls in some positions — prefer positional
  - arrays are value types (mutate inline or return)
  - cross-module free fn(self: Class) loses field mutations — use me-methods

## Scenarios

### CancellationToken

#### new token is not cancelled

- var tok = token new
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tok = token_new()
val c = tok.is_cancelled()
assert_false(c)
```

</details>

#### cancel marks token as cancelled

- var tok = token new
- tok cancel
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tok = token_new()
tok.cancel()
val c = tok.is_cancelled()
assert_true(c)
```

</details>

#### cancel propagates to child token

- var parent = token new
- var child = parent child
- parent cancel
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = token_new()
var child = parent.child()
parent.cancel()
val pc = parent.is_cancelled()
val cc = child.is_cancelled()
assert_true(pc)
assert_true(cc)
```

</details>

#### child not cancelled until parent cancels

- var parent = token new
- var child = parent child
- parent cancel
- assert false
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = token_new()
var child = parent.child()
val cc_before = child.is_cancelled()
parent.cancel()
val cc_after = child.is_cancelled()
assert_false(cc_before)
assert_true(cc_after)
```

</details>

#### cancelling child does not cancel parent

- var parent = token new
- var child = parent child
- child cancel
- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = token_new()
var child = parent.child()
child.cancel()
val cc = child.is_cancelled()
val pc = parent.is_cancelled()
assert_true(cc)
assert_false(pc)
```

</details>

#### multiple children all cancelled when parent cancels

- var parent = token new
- var c0 = parent child
- var c1 = parent child
- var c2 = parent child
- parent cancel
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parent = token_new()
var c0 = parent.child()
var c1 = parent.child()
var c2 = parent.child()
parent.cancel()
val v0 = c0.is_cancelled()
val v1 = c1.is_cancelled()
val v2 = c2.is_cancelled()
assert_true(v0)
assert_true(v1)
assert_true(v2)
```

</details>

#### guard_future pending when not cancelled

- var tok = token new
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tok = token_new()
val f = tok.guard_future()
val p = f.poll()
val pend = p.is_pending()
assert_true(pend)
```

</details>

#### guard_future ready when cancelled

- var tok = token new
- tok cancel
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tok = token_new()
tok.cancel()
val f = tok.guard_future()
val p = f.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### guard_future ready value is true

- var tok = token new
- tok cancel
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tok = token_new()
tok.cancel()
val f = tok.guard_future()
val p = f.poll()
val v = p.unwrap()
assert_true(v)
```

</details>

### AsyncMutex

#### acquire on free mutex returns Ready

- var m = AsyncMutex
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = AsyncMutex(locked: false)
val f = m.acquire()
val p = f.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### acquire on held mutex returns Pending

- var m = AsyncMutex
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = AsyncMutex(locked: true)
val f = m.acquire()
val p = f.poll()
val pend = p.is_pending()
assert_true(pend)
```

</details>

#### try_acquire on free mutex returns true and locks

- var m = AsyncMutex
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = AsyncMutex(locked: false)
val got = m.try_acquire()
val locked_after = m.locked
assert_true(got)
assert_true(locked_after)
```

</details>

#### try_acquire on held mutex returns false

- var m = AsyncMutex
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = AsyncMutex(locked: true)
val got = m.try_acquire()
assert_false(got)
```

</details>

#### release unlocks mutex so next acquire is Ready

- var m = AsyncMutex
- m release
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = AsyncMutex(locked: true)
m.release()
val f = m.acquire()
val p = f.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### acquire locks mutex so second acquire is Pending

- var m = AsyncMutex
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = AsyncMutex(locked: false)
val f1 = m.acquire()
val p1 = f1.poll()
val rdy1 = p1.is_ready()
# mutex is now locked by above acquire
val f2 = m.acquire()
val p2 = f2.poll()
val pend2 = p2.is_pending()
assert_true(rdy1)
assert_true(pend2)
```

</details>

#### release then acquire cycles correctly

- var m = AsyncMutex
- m release
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = AsyncMutex(locked: false)
val f1 = m.acquire()
val p1 = f1.poll()
val rdy1 = p1.is_ready()
m.release()
val f2 = m.acquire()
val p2 = f2.poll()
val rdy2 = p2.is_ready()
assert_true(rdy1)
assert_true(rdy2)
```

</details>

### AsyncSemaphore

#### acquire with permits available returns Ready

- var sem = AsyncSemaphore
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 2, max_permits: 2)
val f = sem.acquire()
val p = f.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### acquire decrements permit count

- var sem = AsyncSemaphore
- assert true
   - Expected: remaining equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 2, max_permits: 2)
val f = sem.acquire()
val p = f.poll()
val rdy = p.is_ready()
val remaining = sem.permits
assert_true(rdy)
expect(remaining).to_equal(1)
```

</details>

#### acquire when no permits returns Pending

- var sem = AsyncSemaphore
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 0, max_permits: 2)
val f = sem.acquire()
val p = f.poll()
val pend = p.is_pending()
assert_true(pend)
```

</details>

#### try_acquire with permits returns true

- var sem = AsyncSemaphore
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 1, max_permits: 1)
val got = sem.try_acquire()
assert_true(got)
```

</details>

#### try_acquire with no permits returns false

- var sem = AsyncSemaphore
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 0, max_permits: 1)
val got = sem.try_acquire()
assert_false(got)
```

</details>

#### release increments permits up to max

- var sem = AsyncSemaphore
- sem release
   - Expected: p1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 0, max_permits: 2)
sem.release()
val p1 = sem.permits
expect(p1).to_equal(1)
```

</details>

#### release clamps at max_permits

- var sem = AsyncSemaphore
- sem release
   - Expected: p equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 2, max_permits: 2)
sem.release()
val p = sem.permits
expect(p).to_equal(2)
```

</details>

#### exhaust all permits then release makes next acquire Ready

- var sem = AsyncSemaphore
- sem release
- assert true
   - Expected: perm_after_acq equals `0`
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sem = AsyncSemaphore(permits: 1, max_permits: 1)
val f1 = sem.acquire()
val p1 = f1.poll()
val rdy1 = p1.is_ready()
val perm_after_acq = sem.permits
sem.release()
val f2 = sem.acquire()
val p2 = f2.poll()
val rdy2 = p2.is_ready()
assert_true(rdy1)
expect(perm_after_acq).to_equal(0)
assert_true(rdy2)
```

</details>

### TimerFuture

#### 0ms timer is immediately ready on first poll

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tf = timer_new(0)
val p = tf.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### 1ms timer with deadline already past is ready

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use negative duration to ensure deadline is in the past
val tf = timer_new(-1)
val p = tf.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### large future deadline is still Pending

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tf = timer_new(999999999)
val p = tf.poll()
val pend = p.is_pending()
assert_true(pend)
```

</details>

#### as_future with 0ms deadline returns Ready future

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tf = timer_new(0)
val f = tf.as_future()
val p = f.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### as_future with large deadline returns Pending future

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tf = timer_new(999999999)
val f = tf.as_future()
val p = f.poll()
val pend = p.is_pending()
assert_true(pend)
```

</details>

### timeout_with_deadline

#### ready inner returns inner value before deadline

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = Future.from_value("done")
val result = timeout_with_deadline(inner, 999999999)
val p = result.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### ready inner value is the inner text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = Future.from_value("hello")
val result = timeout_with_deadline(inner, 999999999)
val p = result.poll()
val v = p.unwrap()
expect(v).to_equal("hello")
```

</details>

#### pending inner with expired deadline returns timed out

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = Future.pending<text>()
# Use negative deadline to simulate already-expired
val result = timeout_with_deadline(inner, -1)
val p = result.poll()
val rdy = p.is_ready()
assert_true(rdy)
```

</details>

#### pending inner expired deadline value is timed out text

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = Future.pending<text>()
val result = timeout_with_deadline(inner, -1)
val p = result.poll()
val v = p.unwrap()
expect(v).to_equal("timed out")
```

</details>

#### pending inner with large deadline returns Pending

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = Future.pending<text>()
val result = timeout_with_deadline(inner, 999999999)
val p = result.poll()
val pend = p.is_pending()
assert_true(pend)
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


</details>
