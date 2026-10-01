# Gpu Scheduler Diag Specification

> Tests covering GPU scheduler std.diag instrumentation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Scheduler Diag Specification

## Scenarios

### GPU scheduler std.diag instrumentation

#### emits a hop line with count evidence at every pure-queue transition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a hop line with count evidence at every pure-queue transition
   - Expected: dbg_last_emit() equals `[event evt-1] enqueue status=queued queued=1 bytes=128`
   - Expected: dbg_last_emit() equals `[event queue] submit submitted=1 in_flight=1`
   - Expected: dbg_last_emit() equals `[event queue] complete completed=1 completed_pending=1`
   - Expected: drain_result.drained equals `1`
   - Expected: dbg_last_emit() equals `[event queue] drain drained=1 status=completed completed=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits a hop line with count evidence at every pure-queue transition")
dbg_diag_reset()
dbg_force_facet("events")

val lane = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, true, 2)
val event = engine2d_host_gpu_event("evt-1", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val state = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)

# EMPTY -> QUEUED: hop keyed by the event id, exact detail incl. queue depth.
val queued = engine2d_host_gpu_pure_queue_emit_payload_text(state, decision, lane, 12345, _DIAG_PAYLOAD)
expect(dbg_last_emit()).to_equal("[event evt-1] enqueue status=queued queued=1 bytes=128")

# QUEUED -> SUBMITTED: real submitted/in-flight counts.
val submitted = engine2d_host_gpu_pure_queue_submit_pending(queued, 1)
expect(dbg_last_emit()).to_equal("[event queue] submit submitted=1 in_flight=1")

# SUBMITTED -> COMPLETED: real completion counts.
val completed = engine2d_host_gpu_pure_queue_complete_pending(submitted, 1)
expect(dbg_last_emit()).to_equal("[event queue] complete completed=1 completed_pending=1")

# COMPLETED -> drained: real drain count + status.
val step = engine2d_host_gpu_pure_queue_drain(completed, 1)
val drain_result = step.result
expect(drain_result.drained).to_equal(1)
expect(dbg_last_emit()).to_equal("[event queue] drain drained=1 status=completed completed=1")
```

</details>

#### emits nothing when every facet is off (zero-overhead proof)

- emits nothing when every facet is off (zero-overhead proof)
   - Expected: drain_result.drained equals `1`
   - Expected: dbg_last_emit() equals ``
   - Expected: dbg_stage_history().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits nothing when every facet is off (zero-overhead proof)")
dbg_diag_reset()

val lane = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, true, 2)
val event = engine2d_host_gpu_event("evt-2", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val state = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)

val queued = engine2d_host_gpu_pure_queue_emit_payload_text(state, decision, lane, 12345, _DIAG_PAYLOAD)
val submitted = engine2d_host_gpu_pure_queue_submit_pending(queued, 1)
val completed = engine2d_host_gpu_pure_queue_complete_pending(submitted, 1)
val step = engine2d_host_gpu_pure_queue_drain(completed, 1)
val drain_result = step.result

# The state machine still advances (queue is honest, not diag-dependent)...
expect(drain_result.drained).to_equal(1)
# ...but with all facets off, diag emitted and recorded absolutely nothing.
expect(dbg_last_emit()).to_equal("")
expect(dbg_stage_history().len()).to_equal(0)
```

</details>

#### keys the enqueue hop by a distinct event id

- keys the enqueue hop by a distinct event id
   - Expected: dbg_last_emit() equals `[event chain-9] enqueue status=queued queued=1 bytes=256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keys the enqueue hop by a distinct event id")
dbg_diag_reset()
dbg_force_facet("events")

val lane = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 256, 4096, false, false, true, 2)
val event = engine2d_host_gpu_event("chain-9", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 256, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val state = engine2d_host_gpu_pure_queue_state("vulkan", 1, 7, 4096)

val queued = engine2d_host_gpu_pure_queue_emit_payload_text(state, decision, lane, 999, _DIAG_PAYLOAD)
expect(dbg_last_emit()).to_equal("[event chain-9] enqueue status=queued queued=1 bytes=256")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU scheduler std.diag instrumentation.
- GPU scheduler std.diag instrumentation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f5d5314759356fc696bed936bc828971bd17a5c051bd75c25463f760778643cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5d5314759356fc696bed936bc828971bd17a5c051bd75c25463f760778643cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5d5314759356fc696bed936bc828971bd17a5c051bd75c25463f760778643cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl
mirror: doc/06_spec/02_integration/lib/gpu/gpu_scheduler_diag_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/gpu/gpu_scheduler_diag_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/gpu/gpu_scheduler_diag_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a hop line with count evidence at every pure-queue transition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits nothing when every facet is off (zero-overhead proof)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keys the enqueue hop by a distinct event id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
