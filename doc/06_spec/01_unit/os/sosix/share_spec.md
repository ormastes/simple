# SOSIX Share Specification

> SOSIX process sharing is immutable-data plus queue coordination.

<!-- sdn-diagram:id=share_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=share_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

share_spec -> std
share_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=share_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX Share Specification

SOSIX process sharing is immutable-data plus queue coordination.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/share_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX process sharing is immutable-data plus queue coordination.

## Scenarios

### SOSIX immutable datasets

#### allows writes before seal and reads after seal

1. sosix share init
   - Expected: handle equals `0`
   - Expected: sosix_dataset_write(handle as u64, 0u64, [1u8, 2u8, 3u8, 4u8]) equals `4`
   - Expected: sosix_dataset_seal(handle as u64) equals `0`
   - Expected: sosix_dataset_is_sealed(handle as u64) is true
   - Expected: sosix_dataset_size(handle as u64) equals `4u64`
   - Expected: sosix_dataset_handle_slot(handle as u64) equals `0`
   - Expected: sosix_dataset_handle_generation(handle as u64) equals `0`
   - Expected: sosix_dataset_read_byte(handle as u64, 2u64) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val handle = sosix_dataset_create(4u64, 0)

expect(handle).to_equal(0)
expect(sosix_dataset_write(handle as u64, 0u64, [1u8, 2u8, 3u8, 4u8])).to_equal(4)
expect(sosix_dataset_seal(handle as u64)).to_equal(0)
expect(sosix_dataset_is_sealed(handle as u64)).to_equal(true)
expect(sosix_dataset_size(handle as u64)).to_equal(4u64)
expect(sosix_dataset_handle_slot(handle as u64)).to_equal(0)
expect(sosix_dataset_handle_generation(handle as u64)).to_equal(0)
expect(sosix_dataset_read_byte(handle as u64, 2u64)).to_equal(3)
```

</details>

#### rejects writes after seal

1. sosix share init
   - Expected: sosix_dataset_seal(handle as u64) equals `0`
   - Expected: sosix_dataset_write(handle as u64, 0u64, [9u8]) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val handle = sosix_dataset_create(2u64, 0)

expect(sosix_dataset_seal(handle as u64)).to_equal(0)
expect(sosix_dataset_write(handle as u64, 0u64, [9u8])).to_equal(0 - EINVAL as i64)
```

</details>

#### rejects invalid dataset reads

1. sosix share init
   - Expected: sosix_dataset_read_byte(99u64, 0u64) equals `0 - EBADF as i64`
   - Expected: sosix_dataset_create(0u64, 0) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()

expect(sosix_dataset_read_byte(99u64, 0u64)).to_equal(0 - EBADF as i64)
expect(sosix_dataset_create(0u64, 0)).to_equal(0 - EINVAL as i64)
```

</details>

### SOSIX process queues

#### sends and receives FIFO messages

1. sosix share init
   - Expected: queue equals `0`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`
   - Expected: sosix_queue_send(queue as u64, [10u8, 11u8], SOSIX_NO_DATASET) equals `2`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `SOSIX_POLL_READ`
   - Expected: recv.status equals `2`
   - Expected: recv.len equals `2u64`
   - Expected: recv.attached_dataset equals `SOSIX_NO_DATASET`
   - Expected: recv.data[0] equals `10u8`
   - Expected: recv.data[1] equals `11u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(2u64, 8u64, 0)

expect(queue).to_equal(0)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
expect(sosix_queue_send(queue as u64, [10u8, 11u8], SOSIX_NO_DATASET)).to_equal(2)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(SOSIX_POLL_READ)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(2)
expect(recv.len).to_equal(2u64)
expect(recv.attached_dataset).to_equal(SOSIX_NO_DATASET)
expect(recv.data[0]).to_equal(10u8)
expect(recv.data[1]).to_equal(11u8)
```

</details>

#### attaches sealed datasets to queue messages

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [55u8]) equals `1`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [1u8], dataset as u64) equals `1`
   - Expected: recv.status equals `1`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_dataset_read_byte(recv.attached_dataset, 0u64) equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 4u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [55u8])).to_equal(1)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_queue_send(queue as u64, [1u8], dataset as u64)).to_equal(1)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(1)
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_dataset_read_byte(recv.attached_dataset, 0u64)).to_equal(55)
```

</details>

#### rejects unsealed dataset attachments

1. sosix share init
   - Expected: sosix_queue_send(queue as u64, [1u8], dataset as u64) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 4u64, 0)

expect(sosix_queue_send(queue as u64, [1u8], dataset as u64)).to_equal(0 - EINVAL as i64)
```

</details>

#### reports full and empty queue readiness

1. sosix share init
   - Expected: sosix_queue_recv(queue as u64).status equals `0 - EAGAIN as i64`
   - Expected: sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET) equals `1`
   - Expected: sosix_queue_send(queue as u64, [2u8], SOSIX_NO_DATASET) equals `0 - EAGAIN as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 4u64, 0)

expect(sosix_queue_recv(queue as u64).status).to_equal(0 - EAGAIN as i64)
expect(sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET)).to_equal(1)
expect(sosix_queue_send(queue as u64, [2u8], SOSIX_NO_DATASET)).to_equal(0 - EAGAIN as i64)
```

</details>

#### reports HUP after send-side close

1. sosix share init
   - Expected: sosix_queue_close(queue as u64, SOSIX_QUEUE_CLOSE_SEND) equals `0`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_HUP equals `SOSIX_POLL_HUP`
   - Expected: sosix_queue_recv(queue as u64).status equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 4u64, 0)

expect(sosix_queue_close(queue as u64, SOSIX_QUEUE_CLOSE_SEND)).to_equal(0)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_HUP).to_equal(SOSIX_POLL_HUP)
expect(sosix_queue_recv(queue as u64).status).to_equal(0)
```

</details>

#### closes datasets and rejects later use

1. sosix share init
   - Expected: sosix_dataset_close(dataset as u64) equals `0`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0 - EBADF as i64`
   - Expected: sosix_dataset_handle_slot(second as u64) equals `0`
   - Expected: sosix_dataset_handle_generation(second as u64) equals `1`
   - Expected: second equals `65536`
   - Expected: sosix_dataset_read_byte(dataset as u64, 0u64) equals `0 - EBADF as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)

expect(sosix_dataset_close(dataset as u64)).to_equal(0)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0 - EBADF as i64)

val second = sosix_dataset_create(1u64, 0)
expect(sosix_dataset_handle_slot(second as u64)).to_equal(0)
expect(sosix_dataset_handle_generation(second as u64)).to_equal(1)
expect(second).to_equal(65536)
expect(sosix_dataset_read_byte(dataset as u64, 0u64)).to_equal(0 - EBADF as i64)
```

</details>

#### rejects stale queue handles after full close

1. sosix share init
   - Expected: sosix_queue_handle_slot(queue as u64) equals `0`
   - Expected: sosix_queue_handle_generation(queue as u64) equals `0`
   - Expected: sosix_queue_close(queue as u64, 0) equals `0`
   - Expected: sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET) equals `0 - EBADF as i64`
   - Expected: sosix_queue_handle_slot(second as u64) equals `0`
   - Expected: sosix_queue_handle_generation(second as u64) equals `1`
   - Expected: second equals `65536`
   - Expected: sosix_queue_recv(queue as u64).status equals `0 - EBADF as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 4u64, 0)

expect(sosix_queue_handle_slot(queue as u64)).to_equal(0)
expect(sosix_queue_handle_generation(queue as u64)).to_equal(0)
expect(sosix_queue_close(queue as u64, 0)).to_equal(0)
expect(sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET)).to_equal(0 - EBADF as i64)

val second = sosix_queue_create(1u64, 4u64, 0)
expect(sosix_queue_handle_slot(second as u64)).to_equal(0)
expect(sosix_queue_handle_generation(second as u64)).to_equal(1)
expect(second).to_equal(65536)
expect(sosix_queue_recv(queue as u64).status).to_equal(0 - EBADF as i64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
