# Fs Async Specification

> <details>

<!-- sdn-diagram:id=fs_async_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_async_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_async_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_async_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Async Specification

## Scenarios

### SOSIX hosted positioned read over SimpleRing

#### admits a read, services it, and delivers exactly one typed completion

- Reserve and commit a positioned read on the hosted ring
   - Expected: fs.occupancy() equals `1u64`
- Pending polls name the exact ring token that will wake them
   - Expected: check_single_wake(fs, submit) equals `pending-on-own-token`
- Complete the operation and wake exactly one token
   - Expected: fs.pump() equals `1`
   - Expected: fs.telemetry().provider_takes equals `1u64`
   - Expected: fs.telemetry().completions equals `1u64`
   - Expected: fs.telemetry().commits equals `1u64`
   - Expected: completion.transferred equals `16u64`
   - Expected: completion.terminal_state equals `SOSIX_OPERATION_COMPLETED`
- Retire the lease before releasing the slot
   - Expected: fs.occupancy() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SOSIX-FS-ASYNC
step("Reserve and commit a positioned read on the hosted ring")
val fs = setup_sosix_software_ring(2)
val submit = submit_read(fs, 16u64, 0u64)
expect(submit.accepted).to_be(true)
expect(fs.occupancy()).to_equal(1u64)
step("Pending polls name the exact ring token that will wake them")
expect(check_single_wake(fs, submit)).to_equal("pending-on-own-token")
step("Complete the operation and wake exactly one token")
expect(fs.service_one(0, 16u64)).to_be(true)
expect(fs.pump()).to_equal(1)
expect(fs.telemetry().provider_takes).to_equal(1u64)
expect(fs.telemetry().completions).to_equal(1u64)
expect(fs.telemetry().commits).to_equal(1u64)
match fs.poll(submit.operation):
    case TaskPollResult.Ready(result):
        match result:
            case Ok(completion):
                expect(completion.transferred).to_equal(16u64)
                expect(completion.terminal_state).to_equal(SOSIX_OPERATION_COMPLETED)
            case Err(_): fail("completed read reported an error")
    case TaskPollResult.Pending(_): fail("completed read still pending")
step("Retire the lease before releasing the slot")
expect(fs.release(submit.operation).accepted).to_be(true)
expect(fs.occupancy()).to_equal(0u64)
```

</details>

#### retires a canceled submission so its slot can be released

- Cancel before the provider takes the submission
- The provider honors the cancel request and the ring retires the lease
   - Expected: fs.pump() equals `1`
   - Expected: fs.telemetry().cancellations equals `1u64`
- Release succeeds and the slot is free again
   - Expected: fs.occupancy() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cancel before the provider takes the submission")
val fs = setup_sosix_software_ring(1)
val submit = submit_read(fs, 8u64, 0u64)
expect(fs.cancel(submit.operation).accepted).to_be(true)
expect(fs.release(submit.operation).accepted).to_be(false)
step("The provider honors the cancel request and the ring retires the lease")
expect(fs.service_one(0, 8u64)).to_be(true)
expect(fs.pump()).to_equal(1)
expect(fs.telemetry().cancellations).to_equal(1u64)
step("Release succeeds and the slot is free again")
expect(fs.release(submit.operation).accepted).to_be(true)
expect(fs.occupancy()).to_equal(0u64)
```

</details>

#### delivers a completion that arrived before the first poll

- Service and pump before the consumer ever polls
   - Expected: fs.pump() equals `1`
- The first poll observes the result instead of losing it
   - Expected: check_single_wake(fs, submit) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Service and pump before the consumer ever polls")
val fs = setup_sosix_software_ring(1)
val submit = submit_read(fs, 8u64, 0u64)
expect(fs.service_one(0, 8u64)).to_be(true)
expect(fs.pump()).to_equal(1)
step("The first poll observes the result instead of losing it")
expect(check_single_wake(fs, submit)).to_equal("ready")
```

</details>

#### rejects invalid descriptors as values before touching the ring

- Reject an invalid capability and an empty transfer
   - Expected: bad_cap.error.kind equals `SOSIX_ERROR_INVALID_CAPABILITY`
   - Expected: empty.error.kind equals `SOSIX_ERROR_INVALID_BUFFER`
- No slot was reserved for either rejection
   - Expected: fs.occupancy() equals `0u64`
   - Expected: fs.telemetry().reservations equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject an invalid capability and an empty transfer")
val fs = setup_sosix_software_ring(1)
val bad_cap = fs.read_at(SosixCapabilityRef(slot: 0, generation: 0), buffer_ref(), 0u64, 0u64, 8u64, 0u64)
expect(bad_cap.accepted).to_be(false)
expect(bad_cap.error.kind).to_equal(SOSIX_ERROR_INVALID_CAPABILITY)
val empty = submit_read(fs, 0u64, 0u64)
expect(empty.accepted).to_be(false)
expect(empty.error.kind).to_equal(SOSIX_ERROR_INVALID_BUFFER)
step("No slot was reserved for either rejection")
expect(fs.occupancy()).to_equal(0u64)
expect(fs.telemetry().reservations).to_equal(0u64)
```

</details>

#### reports a full queue as a typed error and keeps control of the ring

- Reject a stale generation and a full queue
   - Expected: second.error.kind equals `SOSIX_ERROR_QUEUE_FULL`
   - Expected: fs.occupancy() equals `1u64`
- The admitted operation still completes normally
   - Expected: fs.pump() equals `1`
   - Expected: check_single_wake(fs, first) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a stale generation and a full queue")
val fs = setup_sosix_software_ring(1)
val first = submit_read(fs, 4u64, 0u64)
expect(first.accepted).to_be(true)
val second = submit_read(fs, 4u64, 0u64)
expect(second.accepted).to_be(false)
expect(second.error.kind).to_equal(SOSIX_ERROR_QUEUE_FULL)
expect(fs.occupancy()).to_equal(1u64)
step("The admitted operation still completes normally")
expect(fs.service_one(0, 4u64)).to_be(true)
expect(fs.pump()).to_equal(1)
expect(check_single_wake(fs, first)).to_equal("ready")
```

</details>

#### cannot release a timed-out slot until the ring retires the lease

- Expire the deadline while the provider still owns the submission
   - Expected: expired.slot.state equals `SOSIX_OPERATION_TIMED_OUT`
- Refuse release: the buffer is still leased to the provider
   - Expected: early.reason equals `lease-not-retired`
- A late completion retires the lease without a second terminal result
   - Expected: fs.pump() equals `0`
   - Expected: fs.late_completions equals `1u64`
- Release now succeeds and the slot is free
   - Expected: released.slot.state equals `SOSIX_OPERATION_FREE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Expire the deadline while the provider still owns the submission")
val fs = setup_sosix_software_ring(1)
val submit = submit_read(fs, 32u64, 5u64)
val expired = fs.expire(submit.operation, 10u64)
expect(expired.accepted).to_be(true)
expect(expired.slot.state).to_equal(SOSIX_OPERATION_TIMED_OUT)
step("Refuse release: the buffer is still leased to the provider")
val early = fs.release(submit.operation)
expect(early.accepted).to_be(false)
expect(early.reason).to_equal("lease-not-retired")
step("A late completion retires the lease without a second terminal result")
expect(fs.service_one(0, 32u64)).to_be(true)
expect(fs.pump()).to_equal(0)
expect(fs.late_completions).to_equal(1u64)
match fs.poll(submit.operation):
    case TaskPollResult.Ready(result):
        match result:
            case Ok(_): fail("timed-out read reported success")
            case Err(error): expect(error.transferred).to_equal(0u64)
    case TaskPollResult.Pending(_): fail("timed-out read still pending")
step("Release now succeeds and the slot is free")
val released = fs.release(submit.operation)
expect(released.accepted).to_be(true)
expect(released.slot.state).to_equal(SOSIX_OPERATION_FREE)
```

</details>

#### keeps each operation's result independent of its sibling

- Submit two reads and let the first fail natively
   - Expected: fs.pump() equals `2`
- The failure is typed native and the sibling succeeded
   - Expected: error.kind equals `SOSIX_ERROR_NATIVE`
   - Expected: error.native_code equals `-5`
   - Expected: check_single_wake(fs, second) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit two reads and let the first fail natively")
val fs = setup_sosix_software_ring(2)
val first = submit_read(fs, 8u64, 0u64)
val second = submit_read(fs, 8u64, 0u64)
expect(fs.service_one(-5, 0u64)).to_be(true)
expect(fs.service_one(0, 8u64)).to_be(true)
expect(fs.pump()).to_equal(2)
step("The failure is typed native and the sibling succeeded")
match fs.poll(first.operation):
    case TaskPollResult.Ready(result):
        match result:
            case Ok(_): fail("failed read reported success")
            case Err(error):
                expect(error.kind).to_equal(SOSIX_ERROR_NATIVE)
                expect(error.native_code).to_equal(-5)
    case TaskPollResult.Pending(_): fail("failed read still pending")
expect(check_single_wake(fs, second)).to_equal("ready")
expect(fs.take_completion() != nil).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/sosix/fs_async_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOSIX hosted positioned read over SimpleRing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `c12286dfe079c25323514fab2594c05a922816579d6ee41c87bd25aee327e6d7`
