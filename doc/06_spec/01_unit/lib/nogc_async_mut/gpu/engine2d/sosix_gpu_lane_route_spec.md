# SOSIX GPU Lane Routing Spec — browser (nogc) twin (#39 Gap #2)

> Proves the SOSIX seal-before-share routing on the `nogc_async_mut` twin — the lane the browser backend imports. Mirrors the `gc_async_mut` proof: seal a draw-IR payload and route it through the EXISTING runtime GPU queue (emit -> runtime_drain, COMPLETED=3) with the bytes recovered intact and content identity re-derived from the recovered bytes. This is the mechanism the live browser dispatch site (`browser_backend_dispatch_prepared_draw_ir`) uses when `SIMPLE_SOSIX_GPU_LANE=1`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX GPU Lane Routing Spec — browser (nogc) twin (#39 Gap #2)

Proves the SOSIX seal-before-share routing on the `nogc_async_mut` twin — the lane the browser backend imports. Mirrors the `gc_async_mut` proof: seal a draw-IR payload and route it through the EXISTING runtime GPU queue (emit -> runtime_drain, COMPLETED=3) with the bytes recovered intact and content identity re-derived from the recovered bytes. This is the mechanism the live browser dispatch site (`browser_backend_dispatch_prepared_draw_ir`) uses when `SIMPLE_SOSIX_GPU_LANE=1`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/scheduling/cpu_gpu_offload_scheduler_plan.md |
| Design | doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves the SOSIX seal-before-share routing on the `nogc_async_mut` twin — the
lane the browser backend imports. Mirrors the `gc_async_mut` proof: seal a
draw-IR payload and route it through the EXISTING runtime GPU queue
(emit -> runtime_drain, COMPLETED=3) with the bytes recovered intact and content
identity re-derived from the recovered bytes. This is the mechanism the live
browser dispatch site (`browser_backend_dispatch_prepared_draw_ir`) uses when
`SIMPLE_SOSIX_GPU_LANE=1`.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/os/scheduling/cpu_gpu_offload_scheduler_plan.md

## Design

**Design:** doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md

## Research

**Research:** N/A

## Examples

Seal a draw-IR v2 payload, route it through a runtime queue (queue 1, backend
handle 7), and assert it drains COMPLETED with the payload recovered byte-intact.

## Scenarios

### SOSIX GPU lane routing — nogc twin (#39 Gap #2)

#### routes a sealed draw-IR payload through the runtime queue to COMPLETED

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes a sealed draw-IR payload through the runtime queue to COMPLETED
   - Expected: routed.drained equals `1`
   - Expected: routed.drain_status equals `completed`
   - Expected: routed.drain_payload_text equals `DRAW_IR_PAYLOAD`
   - Expected: recovered.payload_hash equals `sealed.payload_hash`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes a sealed draw-IR payload through the runtime queue to COMPLETED")
engine2d_host_gpu_runtime_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val sealed = engine2d_host_gpu_seal_draw_ir_payload(DRAW_IR_PAYLOAD)

val routed = engine2d_host_gpu_sosix_lane_route(queue, "evt-nogc-1", "draw_ir_delta", 256, 4096, true, false, false, false, true, 12, DRAW_IR_PAYLOAD)

assert_true(routed.sealed)
assert_true(routed.sealed_hash != 0)
assert_true(routed.submitted)
expect(routed.drained).to_equal(1)
expect(routed.drain_status).to_equal("completed")
assert_true(routed.completed)
expect(routed.drain_payload_text).to_equal(DRAW_IR_PAYLOAD)
val recovered = engine2d_host_gpu_seal_draw_ir_payload(routed.drain_payload_text)
expect(recovered.payload_hash).to_equal(sealed.payload_hash)
engine2d_host_gpu_runtime_reset()
```

</details>

#### falls back to the CPU mirror for a host-mutating op

- falls back to the CPU mirror for a host-mutating op


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the CPU mirror for a host-mutating op")
engine2d_host_gpu_runtime_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val routed = engine2d_host_gpu_sosix_lane_route(queue, "evt-nogc-2", "scroll_commit", 256, 4096, true, true, false, false, true, 12, DRAW_IR_PAYLOAD)
assert_true(routed.sealed)
assert_false(routed.submitted)
assert_false(routed.completed)
engine2d_host_gpu_runtime_reset()
```

</details>

#### keeps the lane opt-in: the flag is off by default

- keeps the lane opt-in: the flag is off by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the lane opt-in: the flag is off by default")
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

- Canonical SPipe generation for source `89584112f067ff6b8fab90b3ed62169e02697d092aad33ad94b5f269013c1557`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89584112f067ff6b8fab90b3ed62169e02697d092aad33ad94b5f269013c1557`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89584112f067ff6b8fab90b3ed62169e02697d092aad33ad94b5f269013c1557`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes a sealed draw-IR payload through the runtime queue to COMPLETED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to the CPU mirror for a host-mutating op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/sosix_gpu_lane_route_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the lane opt-in: the flag is off by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
