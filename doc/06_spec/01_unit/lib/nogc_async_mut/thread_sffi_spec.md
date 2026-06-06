# Thread Sffi Specification

> <details>

<!-- sdn-diagram:id=thread_sffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_sffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_sffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_sffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Sffi Specification

## Scenarios

### Thread Sffi

#### should declare thread management externs

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = thread_sffi_source()
expect(src.contains("extern fn spl_thread_create")).to_equal(true)
expect(src.contains("extern fn spl_thread_join")).to_equal(true)
expect(src.contains("extern fn spl_thread_detach")).to_equal(true)
expect(src.contains("extern fn spl_thread_current_id() -> i64")).to_equal(true)
expect(src.contains("extern fn spl_thread_cpu_count() -> i64")).to_equal(true)
```

</details>

#### should wrap thread handles with validity guards

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = thread_sffi_source()
expect(src.contains("class ThreadHandle")).to_equal(true)
expect(src.contains("static fn invalid() -> ThreadHandle")).to_equal(true)
expect(src.contains("static fn from_raw(handle: i64) -> ThreadHandle")).to_equal(true)
expect(src.contains("fn is_valid() -> bool")).to_equal(true)
expect(src.contains("if not self.is_valid()")).to_equal(true)
```

</details>

#### should expose mutex primitives through handle methods

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = thread_sffi_source()
expect(src.contains("extern fn spl_mutex_create() -> i64")).to_equal(true)
expect(src.contains("class MutexHandle")).to_equal(true)
expect(src.contains("fn lock() -> bool")).to_equal(true)
expect(src.contains("fn try_lock() -> bool")).to_equal(true)
expect(src.contains("fn unlock() -> bool")).to_equal(true)
expect(src.contains("fn mutex_create() -> MutexHandle")).to_equal(true)
```

</details>

#### should expose condition variable wait and wake primitives

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = thread_sffi_source()
expect(src.contains("class CondVarHandle")).to_equal(true)
expect(src.contains("fn wait(mutex: MutexHandle) -> bool")).to_equal(true)
expect(src.contains("fn wait_timeout(mutex: MutexHandle, timeout_ms: i64) -> bool")).to_equal(true)
expect(src.contains("fn signal() -> bool")).to_equal(true)
expect(src.contains("fn broadcast() -> bool")).to_equal(true)
expect(src.contains("fn condvar_create() -> CondVarHandle")).to_equal(true)
```

</details>

#### should retain interpreter backed tls semaphore and event helpers

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = thread_sffi_source()
expect(src.contains("fn tls_key_alloc")).to_equal(true)
expect(src.contains("fn tls_key_set")).to_equal(true)
expect(src.contains("fn tls_key_get")).to_equal(true)
expect(src.contains("fn semaphore_create")).to_equal(true)
expect(src.contains("fn event_wait_create")).to_equal(true)
expect(src.contains("fn event_wait_wait")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Thread Sffi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
