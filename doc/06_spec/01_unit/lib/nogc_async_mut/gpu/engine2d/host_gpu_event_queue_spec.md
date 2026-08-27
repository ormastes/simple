# Host Gpu Event Queue Specification

> Tests covering no-GC host GPU event queue.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Event Queue Specification

## Scenarios

### no-GC host GPU event queue

#### round-trips backend handle and Draw IR payload text through runtime drain

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips backend handle and Draw IR payload text through runtime drain
   - Expected: submitted.packet_id equals `1`
   - Expected: drained.drained equals `1`
   - Expected: drained.last_backend_handle equals `7`
   - Expected: drained.last_payload_hash equals `12345`
   - Expected: dispatched.status equals `dispatched`
   - Expected: dispatched.backend_handle equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips backend handle and Draw IR payload text through runtime drain")
rt_host_gpu_queue_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val lane = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, true, 2)
val event = engine2d_host_gpu_event("evt-1", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val payload = "schema=simple-draw-ir-v2\ncomposition id=evt-1 scene=browser-frame backend=gpu\nbatch id=evt-1 backend=gpu source_kind=gui_ast source_id=evt-1 surface=s component=c commands=1"

val submitted = engine2d_host_gpu_event_submit_to_runtime_payload_text(queue, decision, lane, 12345, payload)
val drained = engine2d_host_gpu_runtime_drain(queue, 1)
val dispatched = engine2d_host_gpu_runtime_dispatch_draw_ir(queue, drained, 12345)

expect(submitted.submitted).to_be(true)
expect(submitted.packet_id).to_equal(1)
expect(drained.drained).to_equal(1)
expect(drained.last_backend_handle).to_equal(7)
expect(drained.last_payload_hash).to_equal(12345)
expect(drained.last_payload_text).to_contain("schema=simple-draw-ir-v2")
expect(dispatched.status).to_equal("dispatched")
expect(dispatched.backend_handle).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering no-GC host GPU event queue.
- no-GC host GPU event queue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aad67f9a3db5190a25407d8bd057f6ee3c92e523553ad8e46458bbbd545ffe13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aad67f9a3db5190a25407d8bd057f6ee3c92e523553ad8e46458bbbd545ffe13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aad67f9a3db5190a25407d8bd057f6ee3c92e523553ad8e46458bbbd545ffe13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips backend handle and Draw IR payload text through runtime drain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
