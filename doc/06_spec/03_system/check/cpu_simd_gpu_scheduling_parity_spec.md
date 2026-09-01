# CPU-SIMD/GPU Scheduling Parity Contract

> This is the focused scheduling companion to the CPU-SIMD render scale and cross-arch binary gates. It uses the pure Engine2D host/GPU queue model so the normal test run does not depend on a live GPU, but still proves the backend tag, fallback, packet, and drain-order contract that production queues must preserve.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU-SIMD/GPU Scheduling Parity Contract

This is the focused scheduling companion to the CPU-SIMD render scale and cross-arch binary gates. It uses the pure Engine2D host/GPU queue model so the normal test run does not depend on a live GPU, but still proves the backend tag, fallback, packet, and drain-order contract that production queues must preserve.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/08_tracking/bug/cpu_simd_gpu_scheduling_parity_gate_missing_2026-07-09.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/03_system/check/cpu_simd_gpu_scheduling_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is the focused scheduling companion to the CPU-SIMD render scale and
cross-arch binary gates. It uses the pure Engine2D host/GPU queue model so the
normal test run does not depend on a live GPU, but still proves the backend tag,
fallback, packet, and drain-order contract that production queues must preserve.

## Requirements

**Requirements:** N/A

- REQ-CPU-SIMD-SCHED-001: `cpu_simd` drawing work remains a host/direct drawing
  backend path and does not masquerade as a GPU queue packet.
- REQ-CPU-SIMD-SCHED-002: GPU drawing work uses explicit packet scheduling and
  drains only after queued -> submitted -> completed transitions.
- REQ-CPU-SIMD-SCHED-003: The same payload hash/text is preserved through the
  GPU queue drain receipt.

## Plan

**Plan:** doc/08_tracking/bug/cpu_simd_gpu_scheduling_parity_gate_missing_2026-07-09.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_gpu_scheduling_parity_spec.spl --mode=interpreter --clean
```

## Scenarios

### CPU-SIMD GPU scheduling parity

#### keeps CPU-SIMD drawing direct while GPU drawing queues and drains the same payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps CPU-SIMD drawing direct while GPU drawing queues and drains the same payload
- CPU-SIMD is a drawing backend and stays on the host/direct path
   - Expected: cpu_backend.lane equals `ENGINE2D_BACKEND_LANE_DRAWING`
   - Expected: cpu_backend.backend_name equals `cpu_simd`
   - Expected: cpu_lane.execution_kind equals `ENGINE2D_HOST_GPU_EXEC_DIRECT`
- GPU uses an explicit packet and only drains after submit and complete
   - Expected: gpu_lane.execution_kind equals `ENGINE2D_HOST_GPU_EXEC_PACKET`
   - Expected: queued.queued_count equals `1`
   - Expected: queued.last_status_code equals `1`
   - Expected: submitted.in_flight_count equals `1`
   - Expected: submitted.last_status_code equals `2`
   - Expected: completed.completed_pending_count equals `1`
   - Expected: completed.last_status_code equals `3`
   - Expected: drained.result.drained equals `1`
   - Expected: drained.result.status equals `completed`
   - Expected: drained.result.last_backend_handle equals `7`
   - Expected: drained.result.last_payload_hash equals `DRAW_PAYLOAD_HASH`
   - Expected: drained.result.last_payload_text equals `DRAW_PAYLOAD`
   - Expected: drained.state.completed_pending_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps CPU-SIMD drawing direct while GPU drawing queues and drains the same payload")
step("CPU-SIMD is a drawing backend and stays on the host/direct path")
val cpu_backend = engine2d_drawing_backend_lane("cpu_simd")
val cpu_lane = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_HOST,
    "draw_ir_delta",
    128,
    4096,
    false,
    false,
    true,
    5
)

expect(cpu_backend.lane).to_equal(ENGINE2D_BACKEND_LANE_DRAWING)
expect(cpu_backend.backend_name).to_equal("cpu_simd")
expect(cpu_lane.ok).to_be(true)
expect(cpu_lane.execution_kind).to_equal(ENGINE2D_HOST_GPU_EXEC_DIRECT)
expect(cpu_lane.committed_on_host).to_be(true)
expect(cpu_lane.gpu_batched).to_be(false)
expect(cpu_lane.fallback_explicit).to_be(false)

step("GPU uses an explicit packet and only drains after submit and complete")
val gpu_lane = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    4096,
    false,
    false,
    true,
    5
)
val event = engine2d_host_gpu_event("evt-cpu-simd-gpu-scheduling", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, gpu_lane)
val fresh = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)
val queued = engine2d_host_gpu_pure_queue_emit_payload_text(fresh, decision, gpu_lane, DRAW_PAYLOAD_HASH, DRAW_PAYLOAD)
val submitted = engine2d_host_gpu_pure_queue_submit_pending(queued, 1)
val completed = engine2d_host_gpu_pure_queue_complete_pending(submitted, 1)
val drained = engine2d_host_gpu_pure_queue_drain(completed, 1)

expect(gpu_lane.ok).to_be(true)
expect(gpu_lane.execution_kind).to_equal(ENGINE2D_HOST_GPU_EXEC_PACKET)
expect(gpu_lane.gpu_batched).to_be(true)
expect(gpu_lane.fallback_explicit).to_be(false)
expect(decision.accepted).to_be(true)
expect(decision.queue_required).to_be(true)
expect(queued.queued_count).to_equal(1)
expect(queued.last_status_code).to_equal(1)
expect(submitted.in_flight_count).to_equal(1)
expect(submitted.last_status_code).to_equal(2)
expect(completed.completed_pending_count).to_equal(1)
expect(completed.last_status_code).to_equal(3)
expect(drained.result.drained).to_equal(1)
expect(drained.result.status).to_equal("completed")
expect(drained.result.last_backend_handle).to_equal(7)
expect(drained.result.last_payload_hash).to_equal(DRAW_PAYLOAD_HASH)
expect(drained.result.last_payload_text).to_equal(DRAW_PAYLOAD)
expect(drained.state.completed_pending_count).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/08_tracking/bug/cpu_simd_gpu_scheduling_parity_gate_missing_2026-07-09.md`
- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-CPU-SIMD-SCHED-001:`
- `REQ-CPU-SIMD-SCHED-002:`
- `REQ-CPU-SIMD-SCHED-003:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe7649ef3077db72f01bf98bbcbe8bb3307817e907fa7c31f1ec052d6bec9a99`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe7649ef3077db72f01bf98bbcbe8bb3307817e907fa7c31f1ec052d6bec9a99`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe7649ef3077db72f01bf98bbcbe8bb3307817e907fa7c31f1ec052d6bec9a99`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/check/cpu_simd_gpu_scheduling_parity_spec.spl
mirror: doc/06_spec/03_system/check/cpu_simd_gpu_scheduling_parity_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/cpu_simd_gpu_scheduling_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/cpu_simd_gpu_scheduling_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/cpu_simd_gpu_scheduling_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/cpu_simd_gpu_scheduling_parity_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps CPU-SIMD drawing direct while GPU drawing queues and drains the same payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
