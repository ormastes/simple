# Host/GPU Queue State Machine + CPU<->GPU Round-Trip

> This spec is the state/transport correctness companion to `gpu_scheduler_diag_spec.spl` (which proves the std.diag emission). Here we prove the queue *itself*: the pure state machine EMPTY->QUEUED->SUBMITTED-> COMPLETED walks its legal transitions and rejects every illegal/edge transition the code actually implements; the real runtime-backed queue (`rt_host_gpu_queue_*` via module facades) advances the same state machine through the live channel; and the CPU-side receipt validator (`engine2d_host_gpu_runtime_dispatch_draw_ir`) accepts a correct GPU-echoed receipt yet fails closed on a corrupt payload-hash, a non-Draw-IR schema, or a backend-handle mismatch. The event-flow receipt reports completion ONLY via `committed_on_host`, never via a fabricated GPU-batched claim.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host/GPU Queue State Machine + CPU<->GPU Round-Trip

This spec is the state/transport correctness companion to `gpu_scheduler_diag_spec.spl` (which proves the std.diag emission). Here we prove the queue *itself*: the pure state machine EMPTY->QUEUED->SUBMITTED-> COMPLETED walks its legal transitions and rejects every illegal/edge transition the code actually implements; the real runtime-backed queue (`rt_host_gpu_queue_*` via module facades) advances the same state machine through the live channel; and the CPU-side receipt validator (`engine2d_host_gpu_runtime_dispatch_draw_ir`) accepts a correct GPU-echoed receipt yet fails closed on a corrupt payload-hash, a non-Draw-IR schema, or a backend-handle mismatch. The event-flow receipt reports completion ONLY via `committed_on_host`, never via a fabricated GPU-batched claim.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/gpu/host_gpu_queue_roundtrip_spec.spl` |
| Updated | 2026-07-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec is the state/transport correctness companion to
`gpu_scheduler_diag_spec.spl` (which proves the std.diag emission). Here we
prove the queue *itself*: the pure state machine EMPTY->QUEUED->SUBMITTED->
COMPLETED walks its legal transitions and rejects every illegal/edge transition
the code actually implements; the real runtime-backed queue (`rt_host_gpu_queue_*`
via module facades) advances the same state machine through the live channel; and
the CPU-side receipt validator (`engine2d_host_gpu_runtime_dispatch_draw_ir`)
accepts a correct GPU-echoed receipt yet fails closed on a corrupt payload-hash,
a non-Draw-IR schema, or a backend-handle mismatch. The event-flow receipt reports
completion ONLY via `committed_on_host`, never via a fabricated GPU-batched claim.

## Runtime coverage note (honest)

The full *payload-carrying* live round-trip (`rt_host_gpu_queue_emit_payload_text`,
which threads the backend-handle + payload-hash + Draw-IR text through the runtime)
is NOT exercised here because that extern is currently unregistered in the
self-hosted runner and aborts with `semantic: unknown extern function` — it
regresses the existing `host_gpu_event_queue_spec`, `draw_ir_runtime_queue_spec`
and `browser_backend_runtime_queue_spec`. See bug
`host_gpu_queue_emit_payload_text_extern_unregistered_2026-07-06`. So the transport
round-trip below uses the *registered* header-only emit path (state machine +
counters through the real runtime), and the payload-hash/schema/backend-handle
receipt validation is driven over a synthetic GPU-echoed drain receipt — the exact
struct the runtime hands back — so the fail-closed logic is proven deterministically
and independently of the broken transport extern.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Pure queue | `Engine2dHostGpuPureQueueState` immutable counters; each transition returns a new state |
| Runtime queue | `rt_host_gpu_queue_*` channel reached only through module facade functions |
| Fail-closed | corrupt payload-hash / wrong schema / handle mismatch produce `dispatched=false`, honest status |
| committed_on_host | the only honest source of `completed` in the backward event-flow evidence |

## Related Specifications

- [GPU scheduler diag](../../../02_integration/lib/gpu/gpu_scheduler_diag_spec.spl) — std.diag emission at each transition (complementary)
- [no-GC host GPU event queue](../../../01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl) — narrow runtime round-trip

## Scenarios

### host GPU pure queue — legal transitions

#### walks EMPTY->QUEUED->SUBMITTED->COMPLETED with exact depth after each step

- A fresh pure queue starts EMPTY with zero depth
   - Expected: fresh.queued_count equals `0`
   - Expected: fresh.in_flight_count equals `0`
   - Expected: fresh.completed_pending_count equals `0`
   - Expected: fresh.submitted_count equals `0`
   - Expected: fresh.completed_count equals `0`
   - Expected: fresh.last_status_code equals `0`
- emit enqueues one packet: EMPTY -> QUEUED, status 1
   - Expected: queued.queued_count equals `1`
   - Expected: queued.in_flight_count equals `0`
   - Expected: queued.last_status_code equals `1`
   - Expected: queued.last_payload_hash equals `12345`
- submit moves the packet in-flight: QUEUED -> SUBMITTED, status 2
   - Expected: submitted.queued_count equals `0`
   - Expected: submitted.in_flight_count equals `1`
   - Expected: submitted.submitted_count equals `1`
   - Expected: submitted.last_status_code equals `2`
- complete pends the packet for drain: SUBMITTED -> COMPLETED, status 3
   - Expected: completed.in_flight_count equals `0`
   - Expected: completed.completed_pending_count equals `1`
   - Expected: completed.completed_count equals `1`
   - Expected: completed.last_status_code equals `3`
- drain removes the completed-pending packet and reports it drained
   - Expected: drained.state.completed_pending_count equals `0`
   - Expected: drained.result.drained equals `1`
   - Expected: drained.result.status equals `completed`
   - Expected: drained.result.last_payload_hash equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A fresh pure queue starts EMPTY with zero depth")
val fresh = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
expect(fresh.queued_count).to_equal(0)
expect(fresh.in_flight_count).to_equal(0)
expect(fresh.completed_pending_count).to_equal(0)
expect(fresh.submitted_count).to_equal(0)
expect(fresh.completed_count).to_equal(0)
expect(fresh.last_status_code).to_equal(0)

step("emit enqueues one packet: EMPTY -> QUEUED, status 1")
val decision = accepted_gpu_decision("evt-lifecycle", 128, 4096)
val lane = matching_lane(128, 4096)
val queued = engine2d_host_gpu_pure_queue_emit_payload_text(fresh, decision, lane, 12345, _DRAW_IR_PAYLOAD)
expect(queued.queued_count).to_equal(1)
expect(queued.in_flight_count).to_equal(0)
expect(queued.last_status_code).to_equal(1)
expect(queued.last_payload_hash).to_equal(12345)

step("submit moves the packet in-flight: QUEUED -> SUBMITTED, status 2")
val submitted = engine2d_host_gpu_pure_queue_submit_pending(queued, 1)
expect(submitted.queued_count).to_equal(0)
expect(submitted.in_flight_count).to_equal(1)
expect(submitted.submitted_count).to_equal(1)
expect(submitted.last_status_code).to_equal(2)

step("complete pends the packet for drain: SUBMITTED -> COMPLETED, status 3")
val completed = engine2d_host_gpu_pure_queue_complete_pending(submitted, 1)
expect(completed.in_flight_count).to_equal(0)
expect(completed.completed_pending_count).to_equal(1)
expect(completed.completed_count).to_equal(1)
expect(completed.last_status_code).to_equal(3)

step("drain removes the completed-pending packet and reports it drained")
val drained = engine2d_host_gpu_pure_queue_drain(completed, 1)
expect(drained.state.completed_pending_count).to_equal(0)
expect(drained.result.drained).to_equal(1)
expect(drained.result.status).to_equal("completed")
expect(drained.result.last_payload_hash).to_equal(12345)
```

</details>

### host GPU pure queue — illegal and edge transitions

#### does not enqueue when the decision is not accepted (lane rejected)

- An invalid target lane rejects the schedule, so the decision is not accepted
- assert false
- emit leaves the queue EMPTY and carries the rejection diagnostic
   - Expected: after.queued_count equals `0`
   - Expected: after.last_status_code equals `0`
   - Expected: after.diagnostic equals `invalid target lane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("An invalid target lane rejects the schedule, so the decision is not accepted")
val rejected_lane = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, "bogus", "draw_ir_delta", 128, 4096, false, false, true, 2)
val event = engine2d_host_gpu_event("evt-reject", "bogus", "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, rejected_lane)
assert_false(decision.accepted)

step("emit leaves the queue EMPTY and carries the rejection diagnostic")
val state = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val after = engine2d_host_gpu_pure_queue_emit_payload_text(state, decision, rejected_lane, 12345, _DRAW_IR_PAYLOAD)
expect(after.queued_count).to_equal(0)
expect(after.last_status_code).to_equal(0)
expect(after.diagnostic).to_equal("invalid target lane")
```

</details>

#### does not enqueue a host-committed event (queue not required)

- A host-semantic mutation must commit on host, so queue is not required
- assert true
- assert false
- emit leaves the queue EMPTY with the host-commit diagnostic
   - Expected: after.queued_count equals `0`
   - Expected: after.last_status_code equals `0`
   - Expected: after.diagnostic equals `host semantic mutation must commit on host`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A host-semantic mutation must commit on host, so queue is not required")
val lane = matching_lane(128, 4096)
val event = engine2d_host_gpu_event("evt-host", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, true, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
assert_true(decision.accepted)
assert_false(decision.queue_required)

step("emit leaves the queue EMPTY with the host-commit diagnostic")
val state = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val after = engine2d_host_gpu_pure_queue_emit_payload_text(state, decision, lane, 12345, _DRAW_IR_PAYLOAD)
expect(after.queued_count).to_equal(0)
expect(after.last_status_code).to_equal(0)
expect(after.diagnostic).to_equal("host semantic mutation must commit on host")
```

</details>

#### rejects emit when the backend handle is missing

- A pure queue with backend_handle 0 cannot accept a submit
   - Expected: after.queued_count equals `0`
   - Expected: after.last_status_code equals `0`
   - Expected: after.diagnostic equals `backend handle required for pure queue submit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A pure queue with backend_handle 0 cannot accept a submit")
val decision = accepted_gpu_decision("evt-nohandle", 128, 4096)
val lane = matching_lane(128, 4096)
val no_handle = engine2d_host_gpu_pure_queue_state("vulkan", 1, 0, 4096)
val after = engine2d_host_gpu_pure_queue_emit_payload_text(no_handle, decision, lane, 12345, _DRAW_IR_PAYLOAD)
expect(after.queued_count).to_equal(0)
expect(after.last_status_code).to_equal(0)
expect(after.diagnostic).to_equal("backend handle required for pure queue submit")
```

</details>

#### rejects emit when the packet exceeds the pure queue limit

- An 8000-byte packet against a 4096-byte pure queue is rejected
   - Expected: after.queued_count equals `0`
   - Expected: after.last_status_code equals `0`
   - Expected: after.diagnostic equals `packet exceeds pure queue limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("An 8000-byte packet against a 4096-byte pure queue is rejected")
val big_decision = accepted_gpu_decision("evt-big", 8000, 8192)
val big_lane = matching_lane(8000, 8192)
val small_queue = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val after = engine2d_host_gpu_pure_queue_emit_payload_text(small_queue, big_decision, big_lane, 12345, _DRAW_IR_PAYLOAD)
expect(after.queued_count).to_equal(0)
expect(after.last_status_code).to_equal(0)
expect(after.diagnostic).to_equal("packet exceeds pure queue limit")
```

</details>

#### submit on an EMPTY queue is a no-op that stays EMPTY

- submit_pending on a fresh queue submits nothing
   - Expected: after.in_flight_count equals `0`
   - Expected: after.submitted_count equals `0`
   - Expected: after.last_status_code equals `0`
   - Expected: after.diagnostic equals `pure queue empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("submit_pending on a fresh queue submits nothing")
val fresh = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val after = engine2d_host_gpu_pure_queue_submit_pending(fresh, 1)
expect(after.in_flight_count).to_equal(0)
expect(after.submitted_count).to_equal(0)
expect(after.last_status_code).to_equal(0)
expect(after.diagnostic).to_equal("pure queue empty")
```

</details>

#### complete without a prior submit completes nothing

- A queued-but-not-submitted packet has nothing in flight to complete
   - Expected: after.completed_count equals `0`
   - Expected: after.completed_pending_count equals `0`
   - Expected: after.queued_count equals `1`
   - Expected: after.diagnostic equals `pure queue empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A queued-but-not-submitted packet has nothing in flight to complete")
val decision = accepted_gpu_decision("evt-noc", 128, 4096)
val lane = matching_lane(128, 4096)
val fresh = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val queued = engine2d_host_gpu_pure_queue_emit_payload_text(fresh, decision, lane, 12345, _DRAW_IR_PAYLOAD)
val after = engine2d_host_gpu_pure_queue_complete_pending(queued, 1)
expect(after.completed_count).to_equal(0)
expect(after.completed_pending_count).to_equal(0)
expect(after.queued_count).to_equal(1)
expect(after.diagnostic).to_equal("pure queue empty")
```

</details>

#### a second complete after everything is completed adds nothing

- Drive one packet fully through, then complete again
   - Expected: completed.completed_count equals `1`
   - Expected: again.completed_count equals `1`
   - Expected: again.in_flight_count equals `0`
   - Expected: again.completed_pending_count equals `1`
   - Expected: again.diagnostic equals `pure queue empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drive one packet fully through, then complete again")
val decision = accepted_gpu_decision("evt-dbl", 128, 4096)
val lane = matching_lane(128, 4096)
val fresh = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val queued = engine2d_host_gpu_pure_queue_emit_payload_text(fresh, decision, lane, 12345, _DRAW_IR_PAYLOAD)
val submitted = engine2d_host_gpu_pure_queue_submit_pending(queued, 1)
val completed = engine2d_host_gpu_pure_queue_complete_pending(submitted, 1)
expect(completed.completed_count).to_equal(1)
val again = engine2d_host_gpu_pure_queue_complete_pending(completed, 1)
expect(again.completed_count).to_equal(1)
expect(again.in_flight_count).to_equal(0)
expect(again.completed_pending_count).to_equal(1)
expect(again.diagnostic).to_equal("pure queue empty")
```

</details>

#### drain on an EMPTY queue drains nothing and reports empty

- drain a fresh queue
   - Expected: drained.result.drained equals `0`
   - Expected: drained.result.status equals `empty`
   - Expected: drained.result.last_backend_handle equals `0`
   - Expected: drained.state.completed_pending_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("drain a fresh queue")
val fresh = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val drained = engine2d_host_gpu_pure_queue_drain(fresh, 1)
expect(drained.result.drained).to_equal(0)
expect(drained.result.status).to_equal("empty")
expect(drained.result.last_backend_handle).to_equal(0)
expect(drained.state.completed_pending_count).to_equal(0)
```

</details>

### host GPU runtime queue — CPU<->GPU round-trip

#### round-trips a Draw IR payload: hash, schema and backend handle all validated

- Reset the runtime queue through the module facade (no raw extern)
- engine2d host gpu runtime reset
- Submit a GPU Draw-IR packet with an independent payload-hash literal
- assert true
   - Expected: submitted.status equals `submitted`
   - Expected: submitted.packet_id equals `1`
- Drain the receipt: the GPU echoes back our exact hash, size and schema text
   - Expected: drained.drained equals `1`
   - Expected: drained.status equals `completed`
   - Expected: drained.last_backend_handle equals `7`
   - Expected: drained.last_payload_hash equals `424242`
   - Expected: drained.last_payload_size equals `128`
- Dispatch validates handle + hash + schema and reaches the terminal dispatched state
- assert true
   - Expected: dispatched.status equals `dispatched`
   - Expected: dispatched.backend_handle equals `7`
   - Expected: dispatched.payload_hash equals `424242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reset the runtime queue through the module facade (no raw extern)")
engine2d_host_gpu_runtime_reset()

step("Submit a GPU Draw-IR packet with an independent payload-hash literal")
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val lane = matching_lane(128, 4096)
val event = engine2d_host_gpu_event("evt-rt", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val submitted = engine2d_host_gpu_event_submit_to_runtime_payload_text(queue, decision, lane, 424242, _DRAW_IR_PAYLOAD)
assert_true(submitted.submitted)
expect(submitted.status).to_equal("submitted")
expect(submitted.packet_id).to_equal(1)

step("Drain the receipt: the GPU echoes back our exact hash, size and schema text")
val drained = engine2d_host_gpu_runtime_drain(queue, 1)
expect(drained.drained).to_equal(1)
expect(drained.status).to_equal("completed")
expect(drained.last_backend_handle).to_equal(7)
expect(drained.last_payload_hash).to_equal(424242)
expect(drained.last_payload_size).to_equal(128)
expect(drained.last_payload_text).to_contain("schema=simple-draw-ir-v2")

step("Dispatch validates handle + hash + schema and reaches the terminal dispatched state")
val dispatched = engine2d_host_gpu_runtime_dispatch_draw_ir(queue, drained, 424242)
assert_true(dispatched.dispatched)
expect(dispatched.status).to_equal("dispatched")
expect(dispatched.backend_handle).to_equal(7)
expect(dispatched.payload_hash).to_equal(424242)
```

</details>

### host GPU runtime dispatch — fail-closed on corruption

#### rejects a corrupted payload-hash with no false receipt

- Round-trip a valid packet, then dispatch it claiming the WRONG hash
- engine2d host gpu runtime reset
- assert true
   - Expected: drained.last_payload_hash equals `424242`
- assert false
   - Expected: dispatched.status equals `payload_hash_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Round-trip a valid packet, then dispatch it claiming the WRONG hash")
engine2d_host_gpu_runtime_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val lane = matching_lane(128, 4096)
val event = engine2d_host_gpu_event("evt-badhash", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val submitted = engine2d_host_gpu_event_submit_to_runtime_payload_text(queue, decision, lane, 424242, _DRAW_IR_PAYLOAD)
assert_true(submitted.submitted)
val drained = engine2d_host_gpu_runtime_drain(queue, 1)
expect(drained.last_payload_hash).to_equal(424242)

val dispatched = engine2d_host_gpu_runtime_dispatch_draw_ir(queue, drained, 999999)
assert_false(dispatched.dispatched)
expect(dispatched.status).to_equal("payload_hash_mismatch")
```

</details>

#### rejects a payload that is not Draw IR v2 (wrong schema)

- Submit a non-Draw-IR payload, then attempt dispatch
- engine2d host gpu runtime reset
- assert true
- assert false
- assert false
   - Expected: dispatched.status equals `unsupported_payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a non-Draw-IR payload, then attempt dispatch")
engine2d_host_gpu_runtime_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val lane = matching_lane(128, 4096)
val event = engine2d_host_gpu_event("evt-badschema", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val submitted = engine2d_host_gpu_event_submit_to_runtime_payload_text(queue, decision, lane, 777, _NON_DRAW_IR_PAYLOAD)
assert_true(submitted.submitted)
val drained = engine2d_host_gpu_runtime_drain(queue, 1)
assert_false(drained.last_payload_text.contains("schema=simple-draw-ir-v2"))

val dispatched = engine2d_host_gpu_runtime_dispatch_draw_ir(queue, drained, 777)
assert_false(dispatched.dispatched)
expect(dispatched.status).to_equal("unsupported_payload")
```

</details>

#### rejects a receipt whose backend handle does not match the queue

- Drain a receipt from a handle-7 queue, then dispatch against a handle-9 queue
- engine2d host gpu runtime reset
- assert true
   - Expected: drained.last_backend_handle equals `7`
- assert false
   - Expected: dispatched.status equals `backend_handle_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drain a receipt from a handle-7 queue, then dispatch against a handle-9 queue")
engine2d_host_gpu_runtime_reset()
val queue7 = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val lane = matching_lane(128, 4096)
val event = engine2d_host_gpu_event("evt-mismatch", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val submitted = engine2d_host_gpu_event_submit_to_runtime_payload_text(queue7, decision, lane, 424242, _DRAW_IR_PAYLOAD)
assert_true(submitted.submitted)
val drained = engine2d_host_gpu_runtime_drain(queue7, 1)
expect(drained.last_backend_handle).to_equal(7)

val queue9 = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 9, true, 4096)
val dispatched = engine2d_host_gpu_runtime_dispatch_draw_ir(queue9, drained, 424242)
assert_false(dispatched.dispatched)
expect(dispatched.status).to_equal("backend_handle_mismatch")
```

</details>

### host GPU event-flow — receipt completion is committed_on_host only

#### a GPU-forwarded coarse batch is NOT reported completed (it committed on GPU, not host)

- Route a coarse non-semantic batch to the GPU lane
- assert true
   - Expected: flow.decision.target_lane equals `ENGINE2D_HOST_GPU_LANE_GPU`
- Backward completion is false: gpu_batched no longer counts as completed
- assert false
- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route a coarse non-semantic batch to the GPU lane")
val flow = engine2d_host_gpu_draw_ir_event_flow("evt-fwd", "draw_ir_delta", 128, 4096, true, false, false, false, true, 2)
assert_true(flow.submit.queued)
expect(flow.decision.target_lane).to_equal(ENGINE2D_HOST_GPU_LANE_GPU)
step("Backward completion is false: gpu_batched no longer counts as completed")
assert_false(flow.receipt.committed_on_host)
assert_true(flow.receipt.gpu_batched)
assert_false(flow.receipt.committed_on_host)
```

</details>

#### a host-committed event IS reported completed via committed_on_host

- A host-semantic mutation stays on host and is not forwarded
- assert false
   - Expected: flow.decision.target_lane equals `ENGINE2D_HOST_GPU_LANE_HOST`
- Backward completion is true only because it committed on host
- assert true
- assert true
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A host-semantic mutation stays on host and is not forwarded")
val flow = engine2d_host_gpu_draw_ir_event_flow("evt-host", "draw_ir_delta", 128, 4096, true, true, false, false, true, 2)
assert_false(flow.submit.queued)
expect(flow.decision.target_lane).to_equal(ENGINE2D_HOST_GPU_LANE_HOST)
step("Backward completion is true only because it committed on host")
assert_true(flow.receipt.committed_on_host)
assert_true(flow.receipt.committed_on_host)
assert_false(flow.receipt.gpu_batched)
```

</details>

### Draw IR runtime queue dispatch — honest failure

#### reports failure (not silent success) when the runtime queue is unavailable

- Build a GPU Draw-IR batch but hand it a runtime-unavailable queue
- engine2d host gpu runtime reset
- draw ir rect
- Dispatch neither queues for GPU nor reports a false dispatch
- assert false
- assert false
   - Expected: result.runtime_submit.status equals `runtime_unavailable`
- assert false
   - Expected: result.payload.batch_id equals `evt-unavail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a GPU Draw-IR batch but hand it a runtime-unavailable queue")
engine2d_host_gpu_runtime_reset()
val batch = draw_ir_batch("evt-unavail", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 0, 0, 20, 16, 10, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val dead_queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, false, 4096)

step("Dispatch neither queues for GPU nor reports a false dispatch")
val result = engine2d_draw_ir_runtime_queue_dispatch_only(batch, true, dead_queue)
assert_false(result.queued_for_gpu)
assert_false(result.runtime_submit.submitted)
expect(result.runtime_submit.status).to_equal("runtime_unavailable")
assert_false(result.runtime_dispatch.dispatched)
expect(result.payload.batch_id).to_equal("evt-unavail")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
