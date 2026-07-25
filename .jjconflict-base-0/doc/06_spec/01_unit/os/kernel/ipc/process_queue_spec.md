# Kernel Process Queue Specification

> Bounded MPMC queue model for process-level kernel IPC.

<!-- sdn-diagram:id=process_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_queue_spec -> std
process_queue_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Process Queue Specification

Bounded MPMC queue model for process-level kernel IPC.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/process_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Bounded MPMC queue model for process-level kernel IPC.

## Scenarios

### kernel process queue manager

#### creates handle zero as a valid bounded queue

1. process queue init
   - Expected: queue equals `0`
   - Expected: process_queue_len(queue as u64) equals `0`
   - Expected: process_queue_handle_slot(queue as u64) equals `0`
   - Expected: process_queue_handle_generation(queue as u64) equals `0`
   - Expected: process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_WRITE equals `PROCESS_QUEUE_POLL_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()

val queue = process_queue_create(2u64, 8u64, 0)

expect(queue).to_equal(0)
expect(process_queue_len(queue as u64)).to_equal(0)
expect(process_queue_handle_slot(queue as u64)).to_equal(0)
expect(process_queue_handle_generation(queue as u64)).to_equal(0)
expect(process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_WRITE).to_equal(PROCESS_QUEUE_POLL_WRITE)
```

</details>

#### preserves FIFO message ordering

1. process queue init
   - Expected: process_queue_send(queue as u64, [1u8, 2u8], PROCESS_QUEUE_NO_HANDLE) equals `2`
   - Expected: process_queue_send(queue as u64, [3u8], PROCESS_QUEUE_NO_HANDLE) equals `1`
   - Expected: process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_READ equals `PROCESS_QUEUE_POLL_READ`
   - Expected: first.status equals `2`
   - Expected: first.len equals `2u64`
   - Expected: first.data[0] equals `1u8`
   - Expected: first.data[1] equals `2u8`
   - Expected: second.status equals `1`
   - Expected: second.len equals `1u64`
   - Expected: second.data[0] equals `3u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
val queue = process_queue_create(3u64, 8u64, 0)

expect(process_queue_send(queue as u64, [1u8, 2u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(2)
expect(process_queue_send(queue as u64, [3u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(1)
expect(process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_READ).to_equal(PROCESS_QUEUE_POLL_READ)

val first = process_queue_recv(queue as u64)
expect(first.status).to_equal(2)
expect(first.len).to_equal(2u64)
expect(first.data[0]).to_equal(1u8)
expect(first.data[1]).to_equal(2u8)

val second = process_queue_recv(queue as u64)
expect(second.status).to_equal(1)
expect(second.len).to_equal(1u64)
expect(second.data[0]).to_equal(3u8)
```

</details>

#### returns EAGAIN for full sends and empty receives

1. process queue init
   - Expected: process_queue_recv(queue as u64).status equals `0 - EAGAIN as i64`
   - Expected: process_queue_send(queue as u64, [7u8], PROCESS_QUEUE_NO_HANDLE) equals `1`
   - Expected: process_queue_send(queue as u64, [8u8], PROCESS_QUEUE_NO_HANDLE) equals `0 - EAGAIN as i64`
   - Expected: process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_WRITE equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
val queue = process_queue_create(1u64, 4u64, 0)

expect(process_queue_recv(queue as u64).status).to_equal(0 - EAGAIN as i64)
expect(process_queue_send(queue as u64, [7u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(1)
expect(process_queue_send(queue as u64, [8u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(0 - EAGAIN as i64)
expect(process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_WRITE).to_equal(0)
```

</details>

#### rejects oversized messages

1. process queue init
   - Expected: process_queue_send(queue as u64, [1u8, 2u8, 3u8], PROCESS_QUEUE_NO_HANDLE) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
val queue = process_queue_create(1u64, 2u64, 0)

expect(process_queue_send(queue as u64, [1u8, 2u8, 3u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(0 - EINVAL as i64)
```

</details>

#### preserves attached handles without treating zero as empty

1. process queue init
   - Expected: process_queue_send(queue as u64, [1u8], 0u64) equals `1`
   - Expected: process_queue_send(queue as u64, [2u8], PROCESS_QUEUE_NO_HANDLE) equals `1`
   - Expected: with_handle_zero.status equals `1`
   - Expected: with_handle_zero.attached_handle equals `0u64`
   - Expected: without_handle.status equals `1`
   - Expected: without_handle.attached_handle equals `PROCESS_QUEUE_NO_HANDLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
val queue = process_queue_create(2u64, 4u64, 0)

expect(process_queue_send(queue as u64, [1u8], 0u64)).to_equal(1)
expect(process_queue_send(queue as u64, [2u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(1)

val with_handle_zero = process_queue_recv(queue as u64)
expect(with_handle_zero.status).to_equal(1)
expect(with_handle_zero.attached_handle).to_equal(0u64)

val without_handle = process_queue_recv(queue as u64)
expect(without_handle.status).to_equal(1)
expect(without_handle.attached_handle).to_equal(PROCESS_QUEUE_NO_HANDLE)
```

</details>

#### reports HUP and EOF when the send side is closed

1. process queue init
   - Expected: process_queue_close(queue as u64, PROCESS_QUEUE_CLOSE_SEND) equals `0`
   - Expected: process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_HUP equals `PROCESS_QUEUE_POLL_HUP`
   - Expected: process_queue_recv(queue as u64).status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
val queue = process_queue_create(1u64, 4u64, 0)

expect(process_queue_close(queue as u64, PROCESS_QUEUE_CLOSE_SEND)).to_equal(0)
expect(process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_HUP).to_equal(PROCESS_QUEUE_POLL_HUP)
expect(process_queue_recv(queue as u64).status).to_equal(0)
```

</details>

#### reports HUP when the receive side is closed

1. process queue init
   - Expected: process_queue_close(queue as u64, PROCESS_QUEUE_CLOSE_RECV) equals `0`
   - Expected: process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_HUP equals `PROCESS_QUEUE_POLL_HUP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()
val queue = process_queue_create(1u64, 4u64, 0)

expect(process_queue_close(queue as u64, PROCESS_QUEUE_CLOSE_RECV)).to_equal(0)
expect(process_queue_poll(queue as u64) & PROCESS_QUEUE_POLL_HUP).to_equal(PROCESS_QUEUE_POLL_HUP)
```

</details>

#### returns EBADF and poll error for invalid handles

1. process queue init
   - Expected: process_queue_send(99u64, [1u8], PROCESS_QUEUE_NO_HANDLE) equals `0 - EBADF as i64`
   - Expected: process_queue_recv(99u64).status equals `0 - EBADF as i64`
   - Expected: process_queue_close(99u64, 0) equals `0 - EBADF as i64`
   - Expected: process_queue_poll(99u64) & PROCESS_QUEUE_POLL_ERR equals `PROCESS_QUEUE_POLL_ERR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()

expect(process_queue_send(99u64, [1u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(0 - EBADF as i64)
expect(process_queue_recv(99u64).status).to_equal(0 - EBADF as i64)
expect(process_queue_close(99u64, 0)).to_equal(0 - EBADF as i64)
expect(process_queue_poll(99u64) & PROCESS_QUEUE_POLL_ERR).to_equal(PROCESS_QUEUE_POLL_ERR)
```

</details>

#### rejects stale generation handles after full close and slot reuse

1. process queue init
   - Expected: first equals `0`
   - Expected: process_queue_close(first as u64, 0) equals `0`
   - Expected: process_queue_send(first as u64, [1u8], PROCESS_QUEUE_NO_HANDLE) equals `0 - EBADF as i64`
   - Expected: process_queue_handle_generation(first as u64) equals `0 - EBADF as i64`
   - Expected: process_queue_handle_slot(second as u64) equals `0`
   - Expected: process_queue_handle_generation(second as u64) equals `1`
   - Expected: second equals `65536`
   - Expected: process_queue_recv(first as u64).status equals `0 - EBADF as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
process_queue_init()

val first = process_queue_create(1u64, 4u64, 0)
expect(first).to_equal(0)
expect(process_queue_close(first as u64, 0)).to_equal(0)
expect(process_queue_send(first as u64, [1u8], PROCESS_QUEUE_NO_HANDLE)).to_equal(0 - EBADF as i64)
expect(process_queue_handle_generation(first as u64)).to_equal(0 - EBADF as i64)

val second = process_queue_create(1u64, 4u64, 0)
expect(process_queue_handle_slot(second as u64)).to_equal(0)
expect(process_queue_handle_generation(second as u64)).to_equal(1)
expect(second).to_equal(65536)
expect(process_queue_recv(first as u64).status).to_equal(0 - EBADF as i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
