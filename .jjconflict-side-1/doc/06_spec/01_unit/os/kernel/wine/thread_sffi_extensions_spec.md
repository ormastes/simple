# Thread Sffi Extensions Specification

> 1. fn no destructor

<!-- sdn-diagram:id=thread_sffi_extensions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_sffi_extensions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_sffi_extensions_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_sffi_extensions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Sffi Extensions Specification

## Scenarios

### thread_sffi extensions — TLS keys, semaphore, event-wait

### AC-3: tls_key_alloc / set / get — per-thread storage

#### AC-3: tls_key_alloc returns a positive key

1. fn no destructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
expect(key).to_be_greater_than(0)
```

</details>

#### AC-3: consecutive tls_key_alloc calls return distinct keys

1. fn no destructor
   - Expected: k1 == k2 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_destructor(p: *void) -> void:
    val _ = 0
val k1 = tls_key_alloc(no_destructor)
val k2 = tls_key_alloc(no_destructor)
expect(k1 == k2).to_equal(false)
```

</details>

#### AC-3: tls_key_set and tls_key_get round-trip a value

1. fn no destructor
2. tls key set
   - Expected: got equals `0xABCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
tls_key_set(key, 0xABCD)
val got = tls_key_get(key)
expect(got).to_equal(0xABCD)
```

</details>

#### AC-3: tls_key_get on unused key returns null (0)

1. fn no destructor
   - Expected: got equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
val got = tls_key_get(key)
expect(got).to_equal(0)
```

</details>

#### AC-3: tls_key_set overwrite updates the stored value

1. fn no destructor
2. tls key set
3. tls key set
   - Expected: got equals `0x22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn no_destructor(p: *void) -> void:
    val _ = 0
val key = tls_key_alloc(no_destructor)
tls_key_set(key, 0x11)
tls_key_set(key, 0x22)
val got = tls_key_get(key)
expect(got).to_equal(0x22)
```

</details>

### AC-3: semaphore — create / post / wait

#### AC-3: semaphore_create with initial=0 returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(0)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: semaphore_create with initial=1 returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(1)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: semaphore_create returns distinct handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = semaphore_create(0)
val h2 = semaphore_create(0)
expect(h1 == h2).to_equal(false)
```

</details>

#### AC-3: semaphore_wait with initial=1 and timeout_ns=0 returns signaled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(1)
val result = semaphore_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: semaphore_wait on zero-count semaphore with timeout_ns=0 returns timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(0)
val result = semaphore_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: semaphore_post followed by semaphore_wait returns signaled

1. semaphore post
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(0)
semaphore_post(h)
val result = semaphore_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: semaphore count decrements after successful wait

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = semaphore_create(1)
val r1 = semaphore_wait(h, 0)
expect(r1).to_equal("signaled")
# Count is now 0; next wait should timeout
val r2 = semaphore_wait(h, 0)
expect(r2).to_equal("timeout")
```

</details>

### AC-3: event_wait — create / set / reset / wait

#### AC-3: event_wait_create with manual_reset=false returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(false)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: event_wait_create with manual_reset=true returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(true)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: event_wait_wait on unset event with timeout_ns=0 returns timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(false)
val result = event_wait_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: event_wait_set then event_wait_wait returns signaled

1. event wait set
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(false)
event_wait_set(h)
val result = event_wait_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: manual-reset event remains set after first wait

1. event wait set
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(true)
event_wait_set(h)
val r1 = event_wait_wait(h, 0)
expect(r1).to_equal("signaled")
val r2 = event_wait_wait(h, 0)
expect(r2).to_equal("signaled")
```

</details>

#### AC-3: auto-reset event is consumed after first wait

1. event wait set
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(false)
event_wait_set(h)
val r1 = event_wait_wait(h, 0)
expect(r1).to_equal("signaled")
val r2 = event_wait_wait(h, 0)
expect(r2).to_equal("timeout")
```

</details>

#### AC-3: event_wait_reset on set event causes next wait to timeout

1. event wait set
2. event wait reset
   - Expected: result equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = event_wait_create(true)
event_wait_set(h)
event_wait_reset(h)
val result = event_wait_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/thread_sffi_extensions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- thread_sffi extensions — TLS keys, semaphore, event-wait
- AC-3: tls_key_alloc / set / get — per-thread storage
- AC-3: semaphore — create / post / wait
- AC-3: event_wait — create / set / reset / wait

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
