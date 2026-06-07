# Src Core Facade Specification

> 1. seed

<!-- sdn-diagram:id=src_core_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=src_core_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

src_core_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=src_core_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Src Core Facade Specification

## Scenarios

### gc_async_mut src core facade

#### re-exports context, decorator, random, and regex helpers

1. seed
2. setstate
   - Expected: pattern.get_pattern() equals `ab`
   - Expected: compile("ab").get_pattern() equals `ab`
   - Expected: search("bc", "abc").get() equals `bc`
   - Expected: escape("a.b") equals `a\\.b`
   - Expected: one_or_more(digit()) equals `[0-9]+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = time_now()
val timer = TimerContext.create("facade")
expect(timer.name).to_equal("facade")
expect(time_now()).to_be_greater_than(t0)
val lock = Lock.create()
expect(lock.is_unlocked()).to_equal(true)
val tx = TransactionContext.create()
expect(tx.state).to_equal(TransactionState.Pending)

val cached_fn = CachedFunction(wrapped_fn: nil, cache: {}, hits: 0, misses: 0)
expect(cached_fn.cache_info()["hits"]).to_equal(0)
val logged_fn = LoggedFunction(wrapped_fn: nil, name: "noop", call_count: 0)
expect(logged_fn.call_count).to_equal(0)
val deprecated_fn = DeprecatedFunction(wrapped_fn: nil, message: "old", warned: false)
expect(deprecated_fn.warned).to_equal(false)
val timeout_result = TimeoutResult(value: nil, success: true)
expect(timeout_result.is_success()).to_equal(true)
val timeout_fn = TimeoutFunction(wrapped_fn: nil, timeout_seconds: 10)
expect(timeout_fn.timeout_seconds).to_equal(10)

seed(42)
val state = getstate()
setstate(state)
expect(randrange(0, 10, 1)).to_be_less_than(10)
expect(uniform(0.0, 1.0)).to_be_less_than(1.0)

val pattern = Pattern(pattern: "ab")
expect(pattern.get_pattern()).to_equal("ab")
expect(compile("ab").get_pattern()).to_equal("ab")
expect(search("bc", "abc").get()).to_equal("bc")
expect(escape("a.b")).to_equal("a\\.b")
expect(one_or_more(digit())).to_equal("[0-9]+")
```

</details>

#### re-exports synchronization primitives

1. var atomic = Atomic create
   - Expected: atomic.load() equals `1`
   - Expected: atomic.fetch_add(2) equals `1`
   - Expected: atomic.load() equals `3`
2. var mutex = Mutex create
   - Expected: mutex.try_lock() is true
   - Expected: mutex.is_locked() is true
3. mutex unlock
   - Expected: mutex.is_locked() is false
4. var rw = RwLock create
   - Expected: rw.read() equals `read`
5. rw read unlock
6. rw write
   - Expected: rw.into_inner() equals `write`
7. var sem = Semaphore create
   - Expected: sem.try_acquire(1) is true
   - Expected: sem.available_permits() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atomic = Atomic.create(1)
expect(atomic.load()).to_equal(1)
expect(atomic.fetch_add(2)).to_equal(1)
expect(atomic.load()).to_equal(3)

var mutex = Mutex.create("data")
expect(mutex.try_lock()).to_equal(true)
expect(mutex.is_locked()).to_equal(true)
mutex.unlock()
expect(mutex.is_locked()).to_equal(false)

var rw = RwLock.create("read")
expect(rw.read()).to_equal("read")
rw.read_unlock()
rw.write("write")
expect(rw.into_inner()).to_equal("write")

var sem = Semaphore.create(2)
expect(sem.try_acquire(1)).to_equal(true)
expect(sem.available_permits()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/src/core/src_core_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut src core facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
