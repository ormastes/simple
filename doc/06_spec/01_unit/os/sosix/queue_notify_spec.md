# queue_notify_spec

> @cover src/os/sosix/queue_notify.spl 80%

<!-- sdn-diagram:id=queue_notify_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=queue_notify_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

queue_notify_spec -> std
queue_notify_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=queue_notify_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# queue_notify_spec

@cover src/os/sosix/queue_notify.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/queue_notify_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/os/sosix/queue_notify.spl 80%

SOSIX Queue Notification Specification.

Tests that `queue_notify` correctly allocates per-queue notification objects,
signals recv/send-readiness on send/recv, and that non-blocking poll
functions drain bits correctly. Blocking wait functions are tested in their
non-blocking fast-path (bits already set) since interpreter mode cannot
exercise real scheduler blocking.

## Scenarios

### sosix_queue_notify_init

#### initialises without error

1. sosix queue notify init


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
```

</details>

### sosix_queue_notify_recv signal and poll

#### sets recv bits after notify_recv and clears them after poll

1. sosix queue notify init
2. sosix queue notify recv
   - Expected: bits & SOSIX_NOTIFY_BIT_RECV equals `SOSIX_NOTIFY_BIT_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
sosix_queue_notify_recv(0u64)
val bits = sosix_queue_poll_recv_bits(0u64)
expect(bits & SOSIX_NOTIFY_BIT_RECV).to_equal(SOSIX_NOTIFY_BIT_RECV)
```

</details>

#### clears recv bits after a single poll

1. sosix queue notify init
2. sosix queue notify recv
   - Expected: second equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
sosix_queue_notify_recv(1u64)
val _first = sosix_queue_poll_recv_bits(1u64)
val second = sosix_queue_poll_recv_bits(1u64)
expect(second).to_equal(0u64)
```

</details>

### sosix_queue_notify_send signal and poll

#### sets send bits after notify_send and clears them after poll

1. sosix queue notify init
2. sosix queue notify send
   - Expected: bits & SOSIX_NOTIFY_BIT_SEND equals `SOSIX_NOTIFY_BIT_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
sosix_queue_notify_send(0u64)
val bits = sosix_queue_poll_send_bits(0u64)
expect(bits & SOSIX_NOTIFY_BIT_SEND).to_equal(SOSIX_NOTIFY_BIT_SEND)
```

</details>

#### clears send bits after a single poll

1. sosix queue notify init
2. sosix queue notify send
   - Expected: second equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
sosix_queue_notify_send(2u64)
val _first = sosix_queue_poll_send_bits(2u64)
val second = sosix_queue_poll_send_bits(2u64)
expect(second).to_equal(0u64)
```

</details>

### sosix_queue_wait_recv fast-path

#### returns 0 immediately when recv bits are already set

1. sosix queue notify init
2. sosix queue notify recv
   - Expected: sosix_queue_wait_recv(0u64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
sosix_queue_notify_recv(0u64)
expect(sosix_queue_wait_recv(0u64)).to_equal(0)
```

</details>

### sosix_queue_wait_send fast-path

#### returns 0 immediately when send bits are already set

1. sosix queue notify init
2. sosix queue notify send
   - Expected: sosix_queue_wait_send(0u64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
sosix_queue_notify_send(0u64)
expect(sosix_queue_wait_send(0u64)).to_equal(0)
```

</details>

### sosix_queue_notify out-of-range slot

#### notify_recv on slot >= max is a no-op

1. sosix queue notify init
2. sosix queue notify recv


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
sosix_queue_notify_recv(32u64)
```

</details>

#### wait_recv on slot >= max returns -22

1. sosix queue notify init
   - Expected: sosix_queue_wait_recv(32u64) equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
expect(sosix_queue_wait_recv(32u64)).to_equal(-22)
```

</details>

#### wait_send on slot >= max returns -22

1. sosix queue notify init
   - Expected: sosix_queue_wait_send(32u64) equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_queue_notify_init()
expect(sosix_queue_wait_send(32u64)).to_equal(-22)
```

</details>

### sosix_queue_send wires notify_recv

#### signals recv-ready after a message is enqueued

1. sosix share init
2. sosix queue notify init
   - Expected: sosix_queue_send(queue as u64, [42u8], SOSIX_NO_DATASET) equals `1`
   - Expected: bits & SOSIX_NOTIFY_BIT_RECV equals `SOSIX_NOTIFY_BIT_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
sosix_queue_notify_init()
val queue = sosix_queue_create(2u64, 8u64, 0)
expect(queue).to_be_greater_than(-1)
val slot = queue as u64
val _pre = sosix_queue_poll_recv_bits(slot)
expect(sosix_queue_send(queue as u64, [42u8], SOSIX_NO_DATASET)).to_equal(1)
val bits = sosix_queue_poll_recv_bits(slot)
expect(bits & SOSIX_NOTIFY_BIT_RECV).to_equal(SOSIX_NOTIFY_BIT_RECV)
```

</details>

### sosix_queue_recv wires notify_send

#### signals send-ready after a message is dequeued

1. sosix share init
2. sosix queue notify init
   - Expected: sosix_queue_send(queue as u64, [7u8], SOSIX_NO_DATASET) equals `1`
   - Expected: recv.status equals `1`
   - Expected: send_bits & SOSIX_NOTIFY_BIT_SEND equals `SOSIX_NOTIFY_BIT_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
sosix_queue_notify_init()
val queue = sosix_queue_create(1u64, 8u64, 0)
expect(queue).to_be_greater_than(-1)
val slot = queue as u64
expect(sosix_queue_send(queue as u64, [7u8], SOSIX_NO_DATASET)).to_equal(1)
val _recv_bits = sosix_queue_poll_recv_bits(slot)
val _pre_send = sosix_queue_poll_send_bits(slot)
val recv = sosix_queue_recv(queue as u64)
expect(recv.status).to_equal(1)
val send_bits = sosix_queue_poll_send_bits(slot)
expect(send_bits & SOSIX_NOTIFY_BIT_SEND).to_equal(SOSIX_NOTIFY_BIT_SEND)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
