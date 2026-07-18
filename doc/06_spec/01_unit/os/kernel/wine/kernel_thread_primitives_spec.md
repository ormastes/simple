# Kernel Thread Primitives Specification

> <details>

<!-- sdn-diagram:id=kernel_thread_primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kernel_thread_primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kernel_thread_primitives_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kernel_thread_primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Thread Primitives Specification

## Scenarios

### kernel_thread primitives — M1

### AC-3: kevent — kernel event object

#### AC-3: kevent_create with auto_reset=false returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(false)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_create with auto_reset=true returns a valid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(true)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_create returns distinct handles for separate calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = kevent_create(false)
val h2 = kevent_create(false)
expect(h1 == h2).to_equal(false)
```

</details>

#### AC-3: kevent_set is callable without error on a valid handle

1. kevent set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(false)
kevent_set(h)
# If we reach here, set did not panic
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_reset is callable without error on a valid handle

1. kevent set
2. kevent reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(false)
kevent_set(h)
kevent_reset(h)
expect(h).to_be_greater_than(0)
```

</details>

#### AC-3: kevent_wait with timeout_ns=0 returns immediately with WaitResult value

1. kevent set
   - Expected: result equals `signaled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(false)
kevent_set(h)
# Wait on a set event with 0 timeout: expect signaled
val result = kevent_wait(h, 0)
expect(result).to_equal("signaled")
```

</details>

#### AC-3: kevent_wait on unset event with timeout_ns=0 returns timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(false)
# Event is not set; timeout immediately
val result = kevent_wait(h, 0)
expect(result).to_equal("timeout")
```

</details>

#### AC-3: auto-reset kevent_wait resets the handle after signaled

1. kevent set
   - Expected: r1 equals `signaled`
   - Expected: r2 equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = kevent_create(true)
kevent_set(h)
val r1 = kevent_wait(h, 0)
expect(r1).to_equal("signaled")
# Second wait on auto-reset event: should be timeout (reset already happened)
val r2 = kevent_wait(h, 0)
expect(r2).to_equal("timeout")
```

</details>

### AC-3: kfutex — futex-like wait/wake

#### AC-3: kfutex_wake with count=1 returns the number of woken waiters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No waiters: wake returns 0
val addr: u32 = 0
val woken = kfutex_wake(addr, 1)
expect(woken).to_equal(0)
```

</details>

#### AC-3: kfutex_wait with mismatched expected returns immediately

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If *addr != expected, futex returns immediately with WaitResult.aborted
val addr: u32 = 0
val result = kfutex_wait(addr, 99, 0)
expect(result).to_equal("aborted")
```

</details>

#### AC-3: kfutex_wait with matching expected and timeout_ns=0 returns timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr: u32 = 42
val result = kfutex_wait(addr, 42, 0)
expect(result).to_equal("timeout")
```

</details>

### AC-3: kernel_thread — TLS segment (FS.base)

#### AC-3: kernel_thread_tls_set and tls_get round-trip a value

1. kernel thread tls set
   - Expected: got equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# key=1 (arbitrary), store a sentinel pattern
kernel_thread_tls_set(1, 0xDEADBEEF)
val got = kernel_thread_tls_get(1)
expect(got).to_equal(0xDEADBEEF)
```

</details>

#### AC-3: kernel_thread_tls_get for unset key returns null (0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got = kernel_thread_tls_get(255)
expect(got).to_equal(0)
```

</details>

#### AC-3: kernel_thread_tls_set with key=0 stores and retrieves

1. kernel thread tls set
   - Expected: got equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
kernel_thread_tls_set(0, 0x1234)
val got = kernel_thread_tls_get(0)
expect(got).to_equal(0x1234)
```

</details>

#### AC-3: kernel_thread_create returns a positive Tid

1. fn noop entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# We supply a no-op entry function and stack_size=4096
fn noop_entry() -> void:
    val _ = 0
val tid = kernel_thread_create(noop_entry, 4096)
expect(tid).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/wine/kernel_thread_primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel_thread primitives — M1
- AC-3: kevent — kernel event object
- AC-3: kfutex — futex-like wait/wake
- AC-3: kernel_thread — TLS segment (FS.base)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
