# Green Channel Specification

> Green channels are scheduler-facing contracts for logical green tasks. They do not block carrier workers. Instead, a receive on an empty channel records the task id as parked, and a later send reports which parked task should be unparked. Bounded full sends report backpressure so a scheduler can choose when to retry without stalling the current OS thread.

<!-- sdn-diagram:id=green_channel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_channel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_channel_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_channel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Green Channel Specification

Green channels are scheduler-facing contracts for logical green tasks. They do not block carrier workers. Instead, a receive on an empty channel records the task id as parked, and a later send reports which parked task should be unparked. Bounded full sends report backpressure so a scheduler can choose when to retry without stalling the current OS thread.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/01_unit/lib/nogc_async_mut/green_channel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirements

**Requirements:** N/A

## Overview

Green channels are scheduler-facing contracts for logical green tasks. They do
not block carrier workers. Instead, a receive on an empty channel records the
task id as parked, and a later send reports which parked task should be
unparked. Bounded full sends report backpressure so a scheduler can choose when
to retry without stalling the current OS thread.

## Examples

```simple
val channel = green_channel_new(1)
val parked = green_channel_recv(channel, 41)
val sent = green_channel_send(parked.channel, 99)
expect(sent.receiver_task_id).to_equal(41)
```

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### Green channel contract

#### parks a receiver task when the channel is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = green_channel_new(2)
val received = green_channel_recv(channel, 41)

expect(received.received).to_equal(false)
expect(received.parked).to_equal(true)
expect(received.task_id).to_equal(41)
expect(received.reason).to_equal("parked_on_empty_recv")
expect(green_channel_waiting_count(received.channel)).to_equal(1)
```

</details>

#### send unparks the oldest parked receiver without buffering

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = green_channel_new(2)
val parked = green_channel_recv(channel, 41)
val sent = green_channel_send(parked.channel, 99)

expect(sent.sent).to_equal(true)
expect(sent.unparked).to_equal(true)
expect(sent.receiver_task_id).to_equal(41)
expect(sent.value).to_equal(99)
expect(sent.reason).to_equal("unpark_receiver")
expect(green_channel_waiting_count(sent.channel)).to_equal(0)
expect(green_channel_len(sent.channel)).to_equal(0)
```

</details>

#### receives buffered values in FIFO order without parking

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = green_channel_new(2)
val first_send = green_channel_send(channel, 11)
val second_send = green_channel_send(first_send.channel, 22)
val first_recv = green_channel_recv(second_send.channel, 1)
val second_recv = green_channel_recv(first_recv.channel, 2)

expect(first_recv.received).to_equal(true)
expect(first_recv.parked).to_equal(false)
expect(first_recv.value).to_equal(11)
expect(second_recv.value).to_equal(22)
expect(green_channel_len(second_recv.channel)).to_equal(0)
```

</details>

#### reports bounded backpressure without parking the sender

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel = green_channel_new(1)
val first_send = green_channel_send(channel, 7)
val second_send = green_channel_send(first_send.channel, 8)

expect(second_send.sent).to_equal(false)
expect(second_send.backpressure).to_equal(true)
expect(second_send.sender_should_park).to_equal(false)
expect(second_send.reason).to_equal("bounded_backpressure")
expect(green_channel_len(second_send.channel)).to_equal(1)
expect(green_channel_backpressure_count(second_send.channel)).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
