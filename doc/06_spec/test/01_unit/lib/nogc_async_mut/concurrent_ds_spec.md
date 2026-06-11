# Concurrent Ds Specification

> 1. var q = MpscQueue

<!-- sdn-diagram:id=concurrent_ds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrent_ds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrent_ds_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrent_ds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Ds Specification

## Scenarios

### MpscQueue

#### starts empty

1. var q = MpscQueue
   - Expected: q.is_empty() is true
   - Expected: q.len() equals `0`
2. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpscQueue(_channel_id: rt_channel_new(), _size_handle: rt_atomic_int_new(0))
expect(q.is_empty()).to_equal(true)
expect(q.len()).to_equal(0)
q.close()
```

</details>

#### push and pop single value

1. var q = MpscQueue
2. q push
   - Expected: q.is_empty() is false
   - Expected: q.len() equals `1`
   - Expected: result equals `42`
   - Expected: q.is_empty() is true
3. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpscQueue(_channel_id: rt_channel_new(), _size_handle: rt_atomic_int_new(0))
q.push(42)
expect(q.is_empty()).to_equal(false)
expect(q.len()).to_equal(1)
val result = q.pop()
expect(result).to_equal(42)
expect(q.is_empty()).to_equal(true)
q.close()
```

</details>

#### maintains FIFO order

1. var q = MpscQueue
2. q push
3. q push
4. q push
   - Expected: q.len() equals `3`
   - Expected: q.pop() equals `first`
   - Expected: q.pop() equals `second`
   - Expected: q.pop() equals `third`
   - Expected: q.is_empty() is true
5. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpscQueue(_channel_id: rt_channel_new(), _size_handle: rt_atomic_int_new(0))
q.push("first")
q.push("second")
q.push("third")
expect(q.len()).to_equal(3)
expect(q.pop()).to_equal("first")
expect(q.pop()).to_equal("second")
expect(q.pop()).to_equal("third")
expect(q.is_empty()).to_equal(true)
q.close()
```

</details>

#### pop returns nil when empty

1. var q = MpscQueue
2. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpscQueue(_channel_id: rt_channel_new(), _size_handle: rt_atomic_int_new(0))
val result = q.pop()
expect(result).to_be_nil()
q.close()
```

</details>

#### handles mixed push and pop

1. var q = MpscQueue
2. q push
3. q push
   - Expected: q.pop() equals `1`
4. q push
   - Expected: q.pop() equals `2`
   - Expected: q.pop() equals `3`
5. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpscQueue(_channel_id: rt_channel_new(), _size_handle: rt_atomic_int_new(0))
q.push(1)
q.push(2)
expect(q.pop()).to_equal(1)
q.push(3)
expect(q.pop()).to_equal(2)
expect(q.pop()).to_equal(3)
expect(q.pop()).to_be_nil()
q.close()
```

</details>

### MpmcQueue

#### starts empty

1. var q = MpmcQueue
   - Expected: q.is_empty() is true
   - Expected: q.is_full() is false
   - Expected: q.len() equals `0`
2. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpmcQueue(_channel_id: rt_channel_new(), _capacity: 10, _size_handle: rt_atomic_int_new(0))
expect(q.is_empty()).to_equal(true)
expect(q.is_full()).to_equal(false)
expect(q.len()).to_equal(0)
q.close()
```

</details>

#### push and pop

1. var q = MpmcQueue
   - Expected: pushed is true
   - Expected: q.len() equals `1`
   - Expected: result equals `42`
   - Expected: q.is_empty() is true
2. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpmcQueue(_channel_id: rt_channel_new(), _capacity: 10, _size_handle: rt_atomic_int_new(0))
val pushed = q.push(42)
expect(pushed).to_equal(true)
expect(q.len()).to_equal(1)
val result = q.pop()
expect(result).to_equal(42)
expect(q.is_empty()).to_equal(true)
q.close()
```

</details>

#### rejects push when full

1. var q = MpmcQueue
   - Expected: q.push("a") is true
   - Expected: q.push("b") is true
   - Expected: q.is_full() is true
   - Expected: q.push("c") is false
2. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpmcQueue(_channel_id: rt_channel_new(), _capacity: 2, _size_handle: rt_atomic_int_new(0))
expect(q.push("a")).to_equal(true)
expect(q.push("b")).to_equal(true)
expect(q.is_full()).to_equal(true)
expect(q.push("c")).to_equal(false)
q.close()
```

</details>

#### pop returns nil when empty

1. var q = MpmcQueue
2. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpmcQueue(_channel_id: rt_channel_new(), _capacity: 10, _size_handle: rt_atomic_int_new(0))
val result = q.pop()
expect(result).to_be_nil()
q.close()
```

</details>

#### maintains FIFO order

1. var q = MpmcQueue
2. q push
3. q push
4. q push
   - Expected: q.pop() equals `1`
   - Expected: q.pop() equals `2`
   - Expected: q.pop() equals `3`
5. q close


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = MpmcQueue(_channel_id: rt_channel_new(), _capacity: 10, _size_handle: rt_atomic_int_new(0))
q.push(1)
q.push(2)
q.push(3)
expect(q.pop()).to_equal(1)
expect(q.pop()).to_equal(2)
expect(q.pop()).to_equal(3)
q.close()
```

</details>

### ConcurrentMap

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConcurrentMap(_handle: __rt_hashmap_new())
expect(m.is_empty()).to_equal(true)
expect(m.len()).to_equal(0)
```

</details>

#### inserts and retrieves

1. m insert
   - Expected: m.get("key1") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConcurrentMap(_handle: __rt_hashmap_new())
m.insert("key1", 42)
expect(m.get("key1")).to_equal(42)
```

</details>

#### contains_key

1. m insert
   - Expected: m.has("x") is true
   - Expected: m.has("y") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConcurrentMap(_handle: __rt_hashmap_new())
m.insert("x", 1)
expect(m.has("x")).to_equal(true)
expect(m.has("y")).to_equal(false)
```

</details>

#### removes key

1. m insert
2. m remove
   - Expected: m.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConcurrentMap(_handle: __rt_hashmap_new())
m.insert("a", 10)
m.remove("a")
expect(m.len()).to_equal(0)
```

</details>

#### tracks length

1. m insert
2. m insert
3. m insert
   - Expected: m.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConcurrentMap(_handle: __rt_hashmap_new())
m.insert("a", 1)
m.insert("b", 2)
m.insert("c", 3)
expect(m.len()).to_equal(3)
```

</details>

#### overwrites existing key

1. m insert
2. m insert
   - Expected: m.get("key") equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ConcurrentMap(_handle: __rt_hashmap_new())
m.insert("key", "old")
m.insert("key", "new")
expect(m.get("key")).to_equal("new")
```

</details>

### AtomicFlag

#### starts unset

1. f free


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = AtomicFlag(_handle: rt_atomic_bool_new(false))
expect(f.is_set()).to_equal(false)
f.free()
```

</details>

#### set and clear

1. f set
   - Expected: f.is_set() is true
2. f clear
   - Expected: f.is_set() is false
3. f free


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = AtomicFlag(_handle: rt_atomic_bool_new(false))
f.set()
expect(f.is_set()).to_equal(true)
f.clear()
expect(f.is_set()).to_equal(false)
f.free()
```

</details>

#### test_and_set returns old value

1. f free


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = AtomicFlag(_handle: rt_atomic_bool_new(false))
val was_set = f.test_and_set()
expect(was_set).to_equal(false)
expect(f.is_set()).to_equal(true)
val was_set2 = f.test_and_set()
expect(was_set2).to_equal(true)
f.free()
```

</details>

#### starts set when created with true

1. f free


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = AtomicFlag(_handle: rt_atomic_bool_new(true))
expect(f.is_set()).to_equal(true)
f.free()
```

</details>

### Once

#### starts not completed

1. o free


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = Once(_state: rt_atomic_int_new(0))
expect(o.is_completed()).to_equal(false)
o.free()
```

</details>

#### call_once runs function and marks completed

1. o call once
   - Expected: o.is_completed() is true
   - Expected: rt_atomic_int_load(counter_handle) equals `1`
2. rt atomic int free
3. o free


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counter_handle = rt_atomic_int_new(0)
val o = Once(_state: rt_atomic_int_new(0))
o.call_once(\: rt_atomic_int_fetch_add(counter_handle, 1))
expect(o.is_completed()).to_equal(true)
expect(rt_atomic_int_load(counter_handle)).to_equal(1)
rt_atomic_int_free(counter_handle)
o.free()
```

</details>

#### call_once runs only once

1. o call once
2. o call once
3. o call once
   - Expected: rt_atomic_int_load(counter_handle) equals `1`
4. rt atomic int free
5. o free


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val counter_handle = rt_atomic_int_new(0)
val o = Once(_state: rt_atomic_int_new(0))
o.call_once(\: rt_atomic_int_fetch_add(counter_handle, 1))
o.call_once(\: rt_atomic_int_fetch_add(counter_handle, 1))
o.call_once(\: rt_atomic_int_fetch_add(counter_handle, 1))
expect(rt_atomic_int_load(counter_handle)).to_equal(1)
rt_atomic_int_free(counter_handle)
o.free()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent_ds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MpscQueue
- MpmcQueue
- ConcurrentMap
- AtomicFlag
- Once

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
