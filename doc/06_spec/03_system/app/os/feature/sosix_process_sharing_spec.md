# Sosix Process Sharing Specification

> 1. sosix share init

<!-- sdn-diagram:id=sosix_process_sharing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sosix_process_sharing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sosix_process_sharing_spec -> std
sosix_process_sharing_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sosix_process_sharing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sosix Process Sharing Specification

## Scenarios

### sosix_process_sharing feature spec

### REQ-SOSIX-SHARE-001 immutable datasets

#### should seal a dataset before it becomes readable shared data

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8, 3u8]) equals `3`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_is_sealed(dataset as u64) is true
   - Expected: sosix_dataset_read_byte(dataset as u64, 2u64) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(3u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [1u8, 2u8, 3u8])).to_equal(3)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_dataset_is_sealed(dataset as u64)).to_equal(true)
expect(sosix_dataset_read_byte(dataset as u64, 2u64)).to_equal(3)
```

</details>

#### should reject writes after a dataset is sealed

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_dataset_write(dataset as u64, 1u64, [6u8]) equals `0 - EINVAL as i64`
   - Expected: sosix_dataset_read_byte(dataset as u64, 1u64) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [4u8, 5u8])).to_equal(2)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_dataset_write(dataset as u64, 1u64, [6u8])).to_equal(0 - EINVAL as i64)
expect(sosix_dataset_read_byte(dataset as u64, 1u64)).to_equal(5)
```

</details>

### REQ-SOSIX-SHARE-002 queue transfer

#### should deliver message payloads through a bounded SOSIX queue

1. sosix share init
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`
   - Expected: sosix_queue_send(queue as u64, [10u8, 20u8], SOSIX_NO_DATASET) equals `2`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `SOSIX_POLL_READ`
   - Expected: recv.status equals `2`
   - Expected: recv.data[0] equals `10u8`
   - Expected: recv.data[1] equals `20u8`
   - Expected: recv.attached_dataset equals `SOSIX_NO_DATASET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
expect(sosix_queue_send(queue as u64, [10u8, 20u8], SOSIX_NO_DATASET)).to_equal(2)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(SOSIX_POLL_READ)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(2)
expect(recv.data[0]).to_equal(10u8)
expect(recv.data[1]).to_equal(20u8)
expect(recv.attached_dataset).to_equal(SOSIX_NO_DATASET)
```

</details>

#### should restore write readiness after the queued message is received

1. sosix share init
   - Expected: sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET) equals `1`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `0u32`
   - Expected: sosix_queue_recv(queue as u64).status equals `1`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE equals `SOSIX_POLL_WRITE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [1u8], SOSIX_NO_DATASET)).to_equal(1)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(0u32)
expect(sosix_queue_recv(queue as u64).status).to_equal(1)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_WRITE).to_equal(SOSIX_POLL_WRITE)
```

</details>

### REQ-SOSIX-SHARE-003 dataset attachment

#### should transfer a sealed dataset handle with a queue message

1. sosix share init
   - Expected: sosix_dataset_write(dataset as u64, 0u64, [77u8, 88u8]) equals `2`
   - Expected: sosix_dataset_seal(dataset as u64) equals `0`
   - Expected: sosix_queue_send(queue as u64, [9u8], dataset as u64) equals `1`
   - Expected: recv.status equals `1`
   - Expected: recv.attached_dataset equals `dataset as u64`
   - Expected: sosix_dataset_read_byte(recv.attached_dataset, 1u64) equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(2u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_dataset_write(dataset as u64, 0u64, [77u8, 88u8])).to_equal(2)
expect(sosix_dataset_seal(dataset as u64)).to_equal(0)
expect(sosix_queue_send(queue as u64, [9u8], dataset as u64)).to_equal(1)

val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(1)
expect(recv.attached_dataset).to_equal(dataset as u64)
expect(sosix_dataset_read_byte(recv.attached_dataset, 1u64)).to_equal(88)
```

</details>

#### should reject unsealed dataset handles as queue attachments

1. sosix share init
   - Expected: sosix_queue_send(queue as u64, [3u8], dataset as u64) equals `0 - EINVAL as i64`
   - Expected: sosix_queue_poll(queue as u64) & SOSIX_POLL_READ equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
val dataset = sosix_dataset_create(1u64, 0)
val queue = sosix_queue_create(1u64, 8u64, 0)

expect(sosix_queue_send(queue as u64, [3u8], dataset as u64)).to_equal(0 - EINVAL as i64)
expect(sosix_queue_poll(queue as u64) & SOSIX_POLL_READ).to_equal(0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/sosix_process_sharing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sosix_process_sharing feature spec
- REQ-SOSIX-SHARE-001 immutable datasets
- REQ-SOSIX-SHARE-002 queue transfer
- REQ-SOSIX-SHARE-003 dataset attachment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
