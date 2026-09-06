# Operation Core Specification

> <details>

<!-- sdn-diagram:id=operation_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=operation_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

operation_core_spec -> std
operation_core_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=operation_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Operation Core Specification

## Scenarios

### SOSIX typed operation core

#### completes a partial read and releases with a new generation

- Begin an operation in a free slot
- Complete fewer bytes than requested
   - Expected: completed.slot.state equals `SOSIX_OPERATION_COMPLETED`
- Release the terminal slot
   - Expected: released.slot.state equals `SOSIX_OPERATION_FREE`
   - Expected: released.slot.generation equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Begin an operation in a free slot")
val begin = sosix_operation_begin(4, sosix_operation_slot_new(), 500)
expect(begin.accepted).to_be(true)

step("Complete fewer bytes than requested")
val completed = sosix_operation_complete(begin.slot, begin.operation, 0, 7, 16)
expect(completed.accepted).to_be(true)
expect(completed.slot.state).to_equal(SOSIX_OPERATION_COMPLETED)
expect(completed.slot.partial_progress).to_be(true)

step("Release the terminal slot")
val released = sosix_operation_release(completed.slot, begin.operation)
expect(released.accepted).to_be(true)
expect(released.slot.state).to_equal(SOSIX_OPERATION_FREE)
expect(released.slot.generation).to_equal(2)
```

</details>

#### rejects a stale completion after slot reuse

- Complete and release the first generation
- Begin the reused generation and submit the stale identity
   - Expected: stale.reason equals `stale-generation`
   - Expected: stale.slot.state equals `SOSIX_OPERATION_PENDING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Complete and release the first generation")
val begin = sosix_operation_begin(2, sosix_operation_slot_new(), 0)
val completed = sosix_operation_complete(begin.slot, begin.operation, 0, 8, 8)
val released = sosix_operation_release(completed.slot, begin.operation)

step("Begin the reused generation and submit the stale identity")
val reused = sosix_operation_begin(2, released.slot, 0)
val stale = sosix_operation_complete(reused.slot, begin.operation, 0, 8, 8)
expect(stale.accepted).to_be(false)
expect(stale.reason).to_equal("stale-generation")
expect(stale.slot.state).to_equal(SOSIX_OPERATION_PENDING)
```

</details>

#### makes cancellation terminal and rejects a later completion

- Cancel one pending operation
   - Expected: canceled.slot.state equals `SOSIX_OPERATION_CANCELED`
- Reject a completion racing after cancellation
   - Expected: late.reason equals `operation-not-pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cancel one pending operation")
val begin = sosix_operation_begin(1, sosix_operation_slot_new(), 0)
val canceled = sosix_operation_cancel(begin.slot, begin.operation)
expect(canceled.accepted).to_be(true)
expect(canceled.slot.state).to_equal(SOSIX_OPERATION_CANCELED)

step("Reject a completion racing after cancellation")
val late = sosix_operation_complete(canceled.slot, begin.operation, 0, 3, 3)
expect(late.accepted).to_be(false)
expect(late.reason).to_equal("operation-not-pending")
```

</details>

#### records only monotonic progress before a terminal transition

- Reject a terminal completion that would erase observed progress
   - Expected: regressed_completion.reason equals `progress-regressed`
   - Expected: regressed_completion.slot.state equals `SOSIX_OPERATION_PENDING`
   - Expected: regressed_completion.slot.transferred equals `3`
- Accept a terminal completion at the monotonic progress frontier
   - Expected: terminal.slot.transferred equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val begin = sosix_operation_begin(10, sosix_operation_slot_new(), 0)
val progressed = sosix_operation_record_progress(begin.slot, begin.operation, 3)
expect(progressed.accepted).to_be(true)
expect(progressed.slot.transferred).to_equal(3)
expect(progressed.slot.partial_progress).to_be(true)

val regressed = sosix_operation_record_progress(
    progressed.slot, begin.operation, 2)
expect(regressed.accepted).to_be(false)
expect(regressed.reason).to_equal("progress-regressed")
expect(regressed.slot.transferred).to_equal(3)

step("Reject a terminal completion that would erase observed progress")
val regressed_completion = sosix_operation_complete(
    progressed.slot, begin.operation, 0, 2, 8)
expect(regressed_completion.accepted).to_be(false)
expect(regressed_completion.reason).to_equal("progress-regressed")
expect(regressed_completion.slot.state).to_equal(SOSIX_OPERATION_PENDING)
expect(regressed_completion.slot.transferred).to_equal(3)

step("Accept a terminal completion at the monotonic progress frontier")
val terminal = sosix_operation_complete(
    progressed.slot, begin.operation, 0, 3, 8)
expect(terminal.accepted).to_be(true)
expect(terminal.slot.transferred).to_equal(3)
expect(terminal.slot.partial_progress).to_be(true)
```

</details>

#### retains error progress and rejects impossible transfer counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val begin = sosix_operation_begin(6, sosix_operation_slot_new(), 0)
val partial_error = sosix_operation_complete(
    begin.slot, begin.operation, -5, 3, 8)
expect(partial_error.accepted).to_be(true)
expect(partial_error.slot.state).to_equal(SOSIX_OPERATION_FAILED)
expect(partial_error.slot.transferred).to_equal(3)
expect(partial_error.slot.partial_progress).to_be(true)

val second = sosix_operation_begin(8, sosix_operation_slot_new(), 0)
val oversized = sosix_operation_complete(
    second.slot, second.operation, 0, 9, 8)
expect(oversized.accepted).to_be(false)
expect(oversized.reason).to_equal("transferred-exceeds-request")
expect(oversized.slot.state).to_equal(SOSIX_OPERATION_PENDING)
```

</details>

#### expires only a reached nonzero deadline

- Keep the operation pending before its deadline
   - Expected: early.reason equals `deadline-not-reached`
- Expire it at the deadline
   - Expected: expired.slot.state equals `SOSIX_OPERATION_TIMED_OUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep the operation pending before its deadline")
val begin = sosix_operation_begin(7, sosix_operation_slot_new(), 1000)
val early = sosix_operation_expire_deadline(begin.slot, begin.operation, 999)
expect(early.accepted).to_be(false)
expect(early.reason).to_equal("deadline-not-reached")

step("Expire it at the deadline")
val expired = sosix_operation_expire_deadline(begin.slot, begin.operation, 1000)
expect(expired.accepted).to_be(true)
expect(expired.slot.state).to_equal(SOSIX_OPERATION_TIMED_OUT)
```

</details>

#### validates typed file and buffer references before transport

- Create a bounded read-at request
   - Expected: valid.request.file_offset equals `4096`
   - Expected: valid.request.length equals `8192`
- Reject an ungenerated buffer reference
   - Expected: invalid.reason equals `invalid-buffer-reference`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a bounded read-at request")
val operation = SosixOperationId(slot: 3, generation: 9)
val valid = sosix_file_operation_create(
    operation,
    SOSIX_FS_READ_AT,
    SosixCapabilityRef(slot: 12, generation: 2),
    SosixBufferRef(slot: 5, generation: 4),
    4096,
    0,
    8192,
    50000
)
expect(valid.accepted).to_be(true)
expect(valid.request.file_offset).to_equal(4096)
expect(valid.request.length).to_equal(8192)

step("Reject an ungenerated buffer reference")
val invalid = sosix_file_operation_create(
    operation,
    SOSIX_FS_READ_AT,
    SosixCapabilityRef(slot: 12, generation: 2),
    SosixBufferRef(slot: 5, generation: 0),
    0,
    0,
    32,
    0
)
expect(invalid.accepted).to_be(false)
expect(invalid.reason).to_equal("invalid-buffer-reference")
```

</details>

#### fails closed instead of wrapping when a slot generation is exhausted

- Release a terminal slot whose generation is at the u32 maximum
   - Expected: released.reason equals `generation-exhausted`
- The slot stays terminal so no stale identity can regain validity
   - Expected: released.slot.state equals `SOSIX_OPERATION_COMPLETED`
   - Expected: released.slot.generation equals `4294967295`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Release a terminal slot whose generation is at the u32 maximum")
val exhausted = SosixOperationSlot(
    generation: 4294967295, state: SOSIX_OPERATION_COMPLETED, status: 0,
    transferred: 0, partial_progress: false, cancellation_requested: false, deadline_ns: 0
)
val identity = SosixOperationId(slot: 1, generation: 4294967295)
val released = sosix_operation_release(exhausted, identity)
expect(released.accepted).to_be(false)
expect(released.reason).to_equal("generation-exhausted")
step("The slot stays terminal so no stale identity can regain validity")
expect(released.slot.state).to_equal(SOSIX_OPERATION_COMPLETED)
expect(released.slot.generation).to_equal(4294967295)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/operation_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOSIX typed operation core

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `f6df20094f365cc750f7e4d84b943d02817968ef50c168e3191c829d041a5b14`
