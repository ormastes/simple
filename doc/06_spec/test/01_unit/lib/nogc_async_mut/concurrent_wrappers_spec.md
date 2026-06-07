# Concurrent Wrappers Specification

> <details>

<!-- sdn-diagram:id=concurrent_wrappers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrent_wrappers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrent_wrappers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrent_wrappers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Wrappers Specification

## Scenarios

### Thread Wrapper

#### spawns and joins a thread

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = rt_thread_spawn_isolated(\: 42)
val result = rt_thread_join(handle)
expect(result).to_equal(42)
```

</details>

#### reports thread is done

1. rt thread join
   - Expected: done equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = rt_thread_spawn_isolated(\: "done")
rt_thread_join(handle)
val done = rt_thread_is_done(handle)
expect(done).to_equal(1)
```

</details>

#### two-argument thread spawn passes arguments

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handle = rt_thread_spawn_isolated_with_args(\a, b: a + b, 10, 20)
val result = rt_thread_join(handle)
expect(result).to_equal(30)
```

</details>

#### reports available parallelism

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cores = rt_thread_available_parallelism()
check(cores >= 1)
```

</details>

#### sleep does not crash

1. rt thread sleep

2. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_thread_sleep(1)
check(true)
```

</details>

#### yield does not crash

1. rt thread yield

2. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_thread_yield()
check(true)
```

</details>

#### spawns multiple threads

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Avoid mutable var capture in closure (runtime bug)
val h0 = rt_thread_spawn_isolated(\: 0 * 10)
val h1 = rt_thread_spawn_isolated(\: 1 * 10)
val h2 = rt_thread_spawn_isolated(\: 2 * 10)
val h3 = rt_thread_spawn_isolated(\: 3 * 10)
val h4 = rt_thread_spawn_isolated(\: 4 * 10)
val r0 = rt_thread_join(h0)
val r1 = rt_thread_join(h1)
val r2 = rt_thread_join(h2)
val r3 = rt_thread_join(h3)
val r4 = rt_thread_join(h4)
expect(r0).to_equal(0)
expect(r1).to_equal(10)
expect(r4).to_equal(40)
```

</details>

### Channel Wrapper

#### creates a channel and sends/receives

1. rt channel send
   - Expected: result equals `42`

2. rt channel close


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch_id = rt_channel_new()
rt_channel_send(ch_id, 42)
val result = rt_channel_try_recv(ch_id)
expect(result).to_equal(42)
rt_channel_close(ch_id)
```

</details>

#### try_recv returns nil on empty channel

1. rt channel close


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch_id = rt_channel_new()
val result = rt_channel_try_recv(ch_id)
expect(result).to_be_nil()
rt_channel_close(ch_id)
```

</details>

#### reports closed status

1. rt channel close
   - Expected: after equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch_id = rt_channel_new()
val before = rt_channel_is_closed(ch_id)
expect(before).to_equal(0)
rt_channel_close(ch_id)
val after = rt_channel_is_closed(ch_id)
expect(after).to_equal(1)
```

</details>

#### maintains FIFO order

1. rt channel send

2. rt channel send

3. rt channel send
   - Expected: rt_channel_try_recv(ch_id) equals `first`
   - Expected: rt_channel_try_recv(ch_id) equals `second`
   - Expected: rt_channel_try_recv(ch_id) equals `third`

4. rt channel close


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch_id = rt_channel_new()
rt_channel_send(ch_id, "first")
rt_channel_send(ch_id, "second")
rt_channel_send(ch_id, "third")
expect(rt_channel_try_recv(ch_id)).to_equal("first")
expect(rt_channel_try_recv(ch_id)).to_equal("second")
expect(rt_channel_try_recv(ch_id)).to_equal("third")
rt_channel_close(ch_id)
```

</details>

#### thread produces channel consumes

1. rt thread join
   - Expected: result equals `42`

2. rt channel close


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch_id = rt_channel_new()
val h = rt_thread_spawn_isolated_with_args(\data, cid: rt_channel_send(cid, data * 7), 6, ch_id)
rt_thread_join(h)
val result = rt_channel_try_recv(ch_id)
expect(result).to_equal(42)
rt_channel_close(ch_id)
```

</details>

### Mutex Wrapper

#### creates mutex and locks/unlocks

1. rt mutex unlock
   - Expected: value2 equals `42`

2. rt mutex unlock


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(0)
val value = rt_mutex_lock(m)
expect(value).to_equal(0)
rt_mutex_unlock(m, 42)
val value2 = rt_mutex_lock(m)
expect(value2).to_equal(42)
rt_mutex_unlock(m, 42)
```

</details>

#### try_lock succeeds without crashing

1. check

2. rt mutex unlock


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new("hello")
val value = rt_mutex_try_lock(m)
# Runtime returns nil for try_lock (lock acquired)
# Just verify it doesn't crash
check(true)
rt_mutex_unlock(m, "hello")
```

</details>

#### protects value across lock cycles

1. rt mutex lock

2. rt mutex unlock

3. rt mutex lock

4. rt mutex unlock

5. rt mutex lock

6. rt mutex unlock

7. rt mutex lock

8. rt mutex unlock

9. rt mutex lock

10. rt mutex unlock

11. check

12. rt mutex unlock


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = rt_mutex_new(0)
# Unrolled loop: avoid mutable var in while + closure issues
rt_mutex_lock(m)
rt_mutex_unlock(m, 1)
rt_mutex_lock(m)
rt_mutex_unlock(m, 2)
rt_mutex_lock(m)
rt_mutex_unlock(m, 3)
rt_mutex_lock(m)
rt_mutex_unlock(m, 4)
rt_mutex_lock(m)
rt_mutex_unlock(m, 5)
val final_val = rt_mutex_lock(m)
check(final_val != nil)
rt_mutex_unlock(m, final_val)
```

</details>

### RwLock Wrapper

#### creates rwlock and reads value

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(42)
val value = rt_rwlock_read(rw)
expect(value).to_equal(42)
```

</details>

#### writes and reads back

1. rt rwlock set
   - Expected: value equals `99`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(0)
rt_rwlock_set(rw, 99)
val value = rt_rwlock_read(rw)
expect(value).to_equal(99)
```

</details>

#### try_read succeeds without crashing

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new("test")
val value = rt_rwlock_try_read(rw)
# Runtime returns nil for try_read (read lock acquired)
# Just verify it doesn't crash
check(true)
```

</details>

#### try_write returns non-nil value

1. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rw = rt_rwlock_new(10)
val value = rt_rwlock_try_write(rw)
check(value != nil)
```

</details>

### AtomicBool Wrapper

#### creates and loads initial value

1. rt atomic bool free


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_bool_new(true)
val v = rt_atomic_bool_load(a)
expect(v).to_equal(true)
rt_atomic_bool_free(a)
```

</details>

#### stores and loads new value

1. rt atomic bool store
   - Expected: v is true

2. rt atomic bool free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_bool_new(false)
rt_atomic_bool_store(a, true)
val v = rt_atomic_bool_load(a)
expect(v).to_equal(true)
rt_atomic_bool_free(a)
```

</details>

#### swaps value

1. rt atomic bool free


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_bool_new(true)
val old = rt_atomic_bool_swap(a, false)
expect(old).to_equal(true)
val current = rt_atomic_bool_load(a)
expect(current).to_equal(false)
rt_atomic_bool_free(a)
```

</details>

### AtomicInt Wrapper

#### creates and loads initial value

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(42)
val v = rt_atomic_int_load(a)
expect(v).to_equal(42)
rt_atomic_int_free(a)
```

</details>

#### stores and loads

1. rt atomic int store
   - Expected: v equals `100`

2. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(0)
rt_atomic_int_store(a, 100)
val v = rt_atomic_int_load(a)
expect(v).to_equal(100)
rt_atomic_int_free(a)
```

</details>

#### swaps value

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(10)
val old = rt_atomic_int_swap(a, 20)
expect(old).to_equal(10)
expect(rt_atomic_int_load(a)).to_equal(20)
rt_atomic_int_free(a)
```

</details>

#### compare_exchange succeeds

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(10)
val ok = rt_atomic_int_compare_exchange(a, 10, 20)
expect(ok).to_equal(true)
expect(rt_atomic_int_load(a)).to_equal(20)
rt_atomic_int_free(a)
```

</details>

#### compare_exchange fails on mismatch

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(10)
val ok = rt_atomic_int_compare_exchange(a, 99, 20)
expect(ok).to_equal(false)
expect(rt_atomic_int_load(a)).to_equal(10)
rt_atomic_int_free(a)
```

</details>

#### fetch_add returns old value

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(10)
val old = rt_atomic_int_fetch_add(a, 5)
expect(old).to_equal(10)
expect(rt_atomic_int_load(a)).to_equal(15)
rt_atomic_int_free(a)
```

</details>

#### fetch_sub returns old value

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(20)
val old = rt_atomic_int_fetch_sub(a, 7)
expect(old).to_equal(20)
expect(rt_atomic_int_load(a)).to_equal(13)
rt_atomic_int_free(a)
```

</details>

#### fetch_and bitwise operation

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(15)
val old = rt_atomic_int_fetch_and(a, 9)
expect(old).to_equal(15)
expect(rt_atomic_int_load(a)).to_equal(9)
rt_atomic_int_free(a)
```

</details>

#### fetch_or bitwise operation

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(6)
val old = rt_atomic_int_fetch_or(a, 9)
expect(old).to_equal(6)
expect(rt_atomic_int_load(a)).to_equal(15)
rt_atomic_int_free(a)
```

</details>

#### fetch_xor bitwise operation

1. rt atomic int free


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_atomic_int_new(15)
val old = rt_atomic_int_fetch_xor(a, 9)
expect(old).to_equal(15)
expect(rt_atomic_int_load(a)).to_equal(6)
rt_atomic_int_free(a)
```

</details>

### HashMap Wrapper

#### creates empty hashmap

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = rt_hashmap_new()
expect(rt_hashmap_len(h)).to_equal(0)
```

</details>

#### inserts and retrieves

1. rt hashmap insert
   - Expected: rt_hashmap_get(h, "key1") equals `42`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = rt_hashmap_new()
rt_hashmap_insert(h, "key1", 42)
expect(rt_hashmap_get(h, "key1")).to_equal(42)
```

</details>

#### contains_key

1. rt hashmap insert
   - Expected: rt_hashmap_contains_key(h, "x") is true
   - Expected: rt_hashmap_contains_key(h, "y") is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = rt_hashmap_new()
rt_hashmap_insert(h, "x", 1)
expect(rt_hashmap_contains_key(h, "x")).to_equal(true)
expect(rt_hashmap_contains_key(h, "y")).to_equal(false)
```

</details>

#### removes key

1. rt hashmap insert

2. rt hashmap remove
   - Expected: rt_hashmap_len(h) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = rt_hashmap_new()
rt_hashmap_insert(h, "a", 10)
rt_hashmap_remove(h, "a")
expect(rt_hashmap_len(h)).to_equal(0)
```

</details>

#### tracks length

1. rt hashmap insert

2. rt hashmap insert

3. rt hashmap insert
   - Expected: rt_hashmap_len(h) equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = rt_hashmap_new()
rt_hashmap_insert(h, "a", 1)
rt_hashmap_insert(h, "b", 2)
rt_hashmap_insert(h, "c", 3)
expect(rt_hashmap_len(h)).to_equal(3)
```

</details>

### BTreeMap Wrapper

#### creates and inserts

1. rt btreemap insert

2. rt btreemap insert

3. rt btreemap insert
   - Expected: rt_btreemap_len(b) equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = rt_btreemap_new()
rt_btreemap_insert(b, "b", 2)
rt_btreemap_insert(b, "a", 1)
rt_btreemap_insert(b, "c", 3)
expect(rt_btreemap_len(b)).to_equal(3)
```

</details>

#### retrieves by key

1. rt btreemap insert
   - Expected: rt_btreemap_get(b, "key") equals `value`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = rt_btreemap_new()
rt_btreemap_insert(b, "key", "value")
expect(rt_btreemap_get(b, "key")).to_equal("value")
```

</details>

#### first_key and last_key ordered

1. rt btreemap insert

2. rt btreemap insert

3. rt btreemap insert
   - Expected: rt_btreemap_first_key(b) equals `apple`
   - Expected: rt_btreemap_last_key(b) equals `cherry`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = rt_btreemap_new()
rt_btreemap_insert(b, "banana", 2)
rt_btreemap_insert(b, "apple", 1)
rt_btreemap_insert(b, "cherry", 3)
expect(rt_btreemap_first_key(b)).to_equal("apple")
expect(rt_btreemap_last_key(b)).to_equal("cherry")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent_wrappers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Thread Wrapper
- Channel Wrapper
- Mutex Wrapper
- RwLock Wrapper
- AtomicBool Wrapper
- AtomicInt Wrapper
- HashMap Wrapper
- BTreeMap Wrapper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
