# SOSIX GPU Lane Routing Spec (#39 Gap #2)

> Functional proof that the SIMPLE_SOSIX_GPU_LANE path **migrates the existing GPU offload** onto the seal-before-share protocol: a host draw-IR payload is sealed (Gap #1) and routed through the EXISTING runtime GPU queue (`host_gpu_event_queue.spl` submit -> submit_pending -> complete_pending -> drain, COMPLETED=3). No new queue, no Metal, no backend op-body change — this drives the same runtime queue that `draw_ir_runtime_queue_spec.spl` proves, on a cpu backend with a fixture backend handle, so it is deterministic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX GPU Lane Routing Spec (#39 Gap #2)

Functional proof that the SIMPLE_SOSIX_GPU_LANE path **migrates the existing GPU offload** onto the seal-before-share protocol: a host draw-IR payload is sealed (Gap #1) and routed through the EXISTING runtime GPU queue (`host_gpu_event_queue.spl` submit -> submit_pending -> complete_pending -> drain, COMPLETED=3). No new queue, no Metal, no backend op-body change — this drives the same runtime queue that `draw_ir_runtime_queue_spec.spl` proves, on a cpu backend with a fixture backend handle, so it is deterministic.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/scheduling/cpu_gpu_offload_scheduler_plan.md |
| Design | doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Functional proof that the SIMPLE_SOSIX_GPU_LANE path **migrates the existing GPU
offload** onto the seal-before-share protocol: a host draw-IR payload is sealed
(Gap #1) and routed through the EXISTING runtime GPU queue
(`host_gpu_event_queue.spl` submit -> submit_pending -> complete_pending -> drain,
COMPLETED=3). No new queue, no Metal, no backend op-body change — this drives the
same runtime queue that `draw_ir_runtime_queue_spec.spl` proves, on a cpu backend
with a fixture backend handle, so it is deterministic.

The discriminating assertions are that the bytes and content-hash that come BACK
OUT of the runtime drain equal the sealed buffer's — i.e. the seal-before-share
command buffer survived the queue roundtrip intact.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/os/scheduling/cpu_gpu_offload_scheduler_plan.md

## Design

**Design:** doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md

## Research

**Research:** N/A

## Examples

The scenario seals a draw-IR v2 payload, routes it through an Engine2D host/GPU
runtime queue (queue id 1, backend handle 7), and asserts the drain reports the
sealed payload text and hash and a COMPLETED status. A second scenario confirms
that a host-mutating (ineligible) op is NOT queued and falls back to the CPU
mirror without a fabricated completion.

## Scenarios

### SOSIX GPU lane routing (#39 Gap #2)

#### routes a sealed draw-IR payload through the runtime queue to COMPLETED

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes a sealed draw-IR payload through the runtime queue to COMPLETED
   - Expected: routed.submit_status equals `submitted`
   - Expected: routed.drained equals `1`
   - Expected: routed.drain_status equals `completed`
   - Expected: routed.drain_payload_text equals `DRAW_IR_PAYLOAD`
   - Expected: routed.sealed_hash equals `sealed.payload_hash`
   - Expected: recovered.payload_hash equals `sealed.payload_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes a sealed draw-IR payload through the runtime queue to COMPLETED")
engine2d_host_gpu_runtime_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val sealed = engine2d_host_gpu_seal_draw_ir_payload(DRAW_IR_PAYLOAD)

val routed = engine2d_host_gpu_sosix_lane_route(queue, "evt-sosix-1", "draw_ir_delta", 256, 4096, true, false, false, false, true, 12, DRAW_IR_PAYLOAD)

# sealed before it ever entered the queue
assert_true(routed.sealed)
assert_true(routed.sealed_hash != 0)
# accepted onto the runtime GPU queue and drained to completion
assert_true(routed.submitted)
expect(routed.submit_status).to_equal("submitted")
expect(routed.drained).to_equal(1)
expect(routed.drain_status).to_equal("completed")
assert_true(routed.completed)
# the sealed command buffer survived the queue roundtrip byte-intact
expect(routed.drain_payload_text).to_equal(DRAW_IR_PAYLOAD)
expect(routed.sealed_hash).to_equal(sealed.payload_hash)
# Content identity is RE-DERIVED from the recovered bytes via the pure seal
# rather than trusted from the runtime: the runtime text-emit variant does
# not persist the emitted i64 payload_hash (drain returns 0 for it — tracked
# bug host_gpu_runtime_emit_payload_text_drops_hash). Re-sealing the drained
# text and matching the original hash proves the buffer's identity survived
# without depending on the runtime carrying the hash.
val recovered = engine2d_host_gpu_seal_draw_ir_payload(routed.drain_payload_text)
expect(recovered.payload_hash).to_equal(sealed.payload_hash)
engine2d_host_gpu_runtime_reset()
```

</details>

#### falls back to the CPU mirror for a host-mutating op (no fabricated completion)

- falls back to the CPU mirror for a host-mutating op (no fabricated completion)
   - Expected: routed.drained equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the CPU mirror for a host-mutating op (no fabricated completion)")
engine2d_host_gpu_runtime_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)

# mutates_host_semantics = true -> requested lane is HOST -> not queue-required
val routed = engine2d_host_gpu_sosix_lane_route(queue, "evt-sosix-2", "scroll_commit", 256, 4096, true, true, false, false, true, 12, DRAW_IR_PAYLOAD)

# still sealed (immutability is unconditional), but NOT routed to the GPU queue
assert_true(routed.sealed)
assert_false(routed.submitted)
assert_false(routed.completed)
expect(routed.drained).to_equal(0)
engine2d_host_gpu_runtime_reset()
```

</details>

#### keeps the lane opt-in: the SIMPLE_SOSIX_GPU_LANE flag is off by default

- keeps the lane opt-in: the SIMPLE_SOSIX_GPU_LANE flag is off by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the lane opt-in: the SIMPLE_SOSIX_GPU_LANE flag is off by default")
assert_false(engine2d_sosix_gpu_lane_enabled())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/scheduling/cpu_gpu_offload_scheduler_plan.md`
- **Design:** `doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7fdbcd654a00d875d96b5a0930acab7bb5880d3783de7e0af552904a6f5dcbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7fdbcd654a00d875d96b5a0930acab7bb5880d3783de7e0af552904a6f5dcbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7fdbcd654a00d875d96b5a0930acab7bb5880d3783de7e0af552904a6f5dcbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a sealed draw-IR payload through the runtime queue to COMPLETED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to the CPU mirror for a host-mutating op (no fabricated completion)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the lane opt-in: the SIMPLE_SOSIX_GPU_LANE flag is off by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
