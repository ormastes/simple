# SOSIX Share API Specification

> SOSIX exposes immutable datasets as sealed share handles and bounded queues as

<!-- sdn-diagram:id=share_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=share_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

share_api_spec -> std
share_api_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=share_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX Share API Specification

SOSIX exposes immutable datasets as sealed share handles and bounded queues as

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/share_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX exposes immutable datasets as sealed share handles and bounded queues as
the process-friendly communication primitive. POSIX wrappers can sit above this
surface, but process-sharing behavior is defined here.

## Scenarios

### SOSIX share API immutable dataset lifecycle

#### should create an unsealed dataset and seal it for sharing

1. sosix share init
   - Expected: dataset equals `0`
   - Expected: sosix_dataset_is_sealed(dataset as u64) is false
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [7u8, 8u8, 9u8]) equals `3`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_is_sealed(dataset as u64) is true
   - Expected: sosix_dataset_read_byte(dataset as u64, 1u64) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(3u64, 0)

expect(dataset).to_equal(0)
expect(sosix_dataset_is_sealed(dataset as u64)).to_equal(false)
expect(sosix_dataset_write(dataset as u64, 0u64, [7u8, 8u8, 9u8])).to_equal(3)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_dataset_is_sealed(dataset as u64)).to_equal(true)
expect(sosix_dataset_read_byte(dataset as u64, 1u64)).to_equal(8)
```

</details>

#### should reject mutation after the dataset is sealed

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [3u8]) equals `0 - EINVAL as i64`
   - Expected: sosix_dataset_read_byte(dataset as u64, 0u64) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8])).to_equal(2)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_dataset_write(dataset as u64, 0u64, [3u8])).to_equal(0 - EINVAL as i64)
expect(sosix_dataset_read_byte(dataset as u64, 0u64)).to_equal(1)
```

</details>

### SOSIX share API queue dataset attachments

#### should attach a sealed dataset to a queue message

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [10u8, 11u8, 12u8, 13u8]) equals `4`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [1u8, 2u8], dataset as u64) equals `2`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `SOSIX_POLL_READ`
   - Expected: recv.status equals `2`
   - Expected: recv.len equals `2u64`
   - Expected: recv.data[0] equals `1u8`
   - Expected: recv.data[1] equals `2u8`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_dataset_read_byte(recv.attached_dataset, 3u64) equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(4u64, 0)
val queue = sosix_queue_create(2u64, 8u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [10u8, 11u8, 12u8, 13u8])).to_equal(4)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_queue_send(queue as u64, [1u8, 2u8], dataset as u64)).to_equal(2)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(SOSIX_POLL_READ)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(2)
expect(recv.len).to_equal(2u64)
expect(recv.data[0]).to_equal(1u8)
expect(recv.data[1]).to_equal(2u8)
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_dataset_read_byte(recv.attached_dataset, 3u64)).to_equal(13)
```

</details>

#### should preserve queue write readiness after receiving the attached dataset

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [42u8]) equals `1`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [5u8], dataset as u64) equals `1`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `0u32`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [42u8])).to_equal(1)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_queue_send(queue as u64, [5u8], dataset as u64)).to_equal(1)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(0u32)

val recv = sosix_queue_recv(queue as u64)
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
```

</details>

#### should reject unsealed dataset attachments

1. sosix share init
   - Expected: sosix_queue_send(queue as u64, [9u8], dataset as u64) equals `0 - EINVAL as i64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [9u8], dataset as u64)).to_equal(0 - EINVAL as i64)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(0u32)
```

</details>

#### should allow messages without dataset attachments

1. sosix share init
   - Expected: sosix_queue_send(queue as u64, [99u8], SOSIX_NO_DATASET) equals `1`
   - Expected: recv.status equals `1`
   - Expected: recv.attached_dataset equals `SOSIX_NO_DATASET`
   - Expected: recv.data[0] equals `99u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [99u8], SOSIX_NO_DATASET)).to_equal(1)
val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(1)
expect(recv.attached_dataset).to_equal(SOSIX_NO_DATASET)
expect(recv.data[0]).to_equal(99u8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
