# Host/GPU lane event-flow and grammar contract

> Exercises the parser-acceptance and Engine2D lane-contract surface for the host/GPU lane grammar and event-flow diagnostics described by the host_gpu_lane design contract.

<!-- sdn-diagram:id=host_gpu_lane_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_gpu_lane_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_gpu_lane_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_gpu_lane_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host/GPU lane event-flow and grammar contract

Exercises the parser-acceptance and Engine2D lane-contract surface for the host/GPU lane grammar and event-flow diagnostics described by the host_gpu_lane design contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/host_gpu_lane.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/03_system/feature/language/host_gpu_lane_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the parser-acceptance and Engine2D lane-contract surface for the
host/GPU lane grammar and event-flow diagnostics described by the
host_gpu_lane design contract.

## Syntax

Canonical examples:

```simple
target.later(max_packet: 512) gpu \:
    scene.apply_draw_ir_delta(draw_ir_delta_ref)

target.later(max_packet: 512) host \:
    session.focus(hit.target_id)
```

**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Plan:** doc/03_plan/sys_test/host_gpu_lane.md
**Design:** doc/05_design/host_gpu_lane.md

## Scenario Model

The host/GPU lane feature has two current evidence surfaces:

1. Parser acceptance through `bin/simple check` for canonical syntax.
2. Engine2D lane-contract validation for event-flow and performance semantics.

Parser acceptance verifies that the compact grammar remains a small extension
over existing lambdas. The accepted form places the lane marker after
`later(...)` and before `\:` or `\e:`.

Engine2D lane-contract validation verifies behavior that compiler lowering and
runtime queues must preserve when they land:

- same-lane callbacks can execute directly;
- cross-lane callbacks become queue packets;
- host lane commits host semantic state;
- GPU lane accelerates render/effect/resource batches;
- GPU lane cannot mutate host-owned semantic fields;
- GPU hot-path work must be coarse grained;
- packet sizes remain bounded by declared `max_packet` contracts;
- fallback is explicit evidence rather than silent success;
- estimated GPU batch time must be lower than the CPU baseline when a strict
  backend is available.
- event-flow evidence records event count, Draw IR delta count, packet size,
  event-to-present timing, pixel hash, and speedup.

## Event Flow

Host input starts on the host event lane. A GPU hit-test or render/effect update
may be scheduled with `target.later(...) gpu \:`. If GPU work needs to change
semantic UI state, it must send a host proposal and the final mutation runs
through `target.later(...) host \:`.

The system scenarios intentionally avoid real GPU hardware. They prove the
language surface and lane contract before backend-specific Vulkan, Metal,
WebGPU, CUDA, or DirectX evidence is required.

## Acceptance Matrix

HGL-001 canonical grammar:
`target.later() gpu \:` and `target.later() host \:` must parse through
`bin/simple check`.

HGL-002 host semantic mutation:
host lane code may mutate `state.checked` or focus/session state.

HGL-003 GPU render/effect batch:
GPU lane code may carry coarse Draw IR or DisplayGraphIR batch work with packet
bounds.

HGL-004 GPU semantic mutation rejection:
the lane contract rejects GPU attempts to commit host semantic fields.

HGL-005 per-widget dispatch diagnostic:
the lane contract rejects one GPU `later()` callback per widget in a loop and
requires a batch.

HGL-006 event-flow timing evidence:
a strict GPU batch records lower p50/p95 frame time than the host baseline,
preserves event order, and carries a stable pixel hash.

## Out Of Scope

This spec does not prove native parser lowering, runtime queue transport,
device submission, or GPU readback. Those are tracked by the implementation
plan and perf report. This spec provides the red/green contract that those
later layers must preserve.

## Generated Manual Policy

The generated manual should show the primary flow first:

- canonical syntax accepted;
- host semantic mutation accepted;
- GPU render/effect batch accepted;
- GPU semantic mutation rejected;
- per-widget GPU dispatch rejected.
- event-flow timing evidence recorded.

Executable SSpec remains folded below the manual scenarios. No screenshot,
HTML, or raster evidence is needed because this is a compiler/contract system
test, not a visual UI test.

## Scenarios

### host/GPU lane grammar and event-flow contract

#### should accept canonical gpu and host lane markers after later

- Check the canonical target.later(...) gpu and host grammar
- "target later
- "target later
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the canonical target.later(...) gpu and host grammar")
val source = host_gpu_fixture(
    "target.later() gpu \\:\n" +
    "    val draw_ir_batch = \"DisplayGraphIR batch\"\n" +
    "target.later() host \\:\n" +
    "    val semantic_owner = \"host\"\n"
)

val (stdout, stderr, code) = check_source("canonical_lane_markers", source)

expect(code).to_equal(0)
expect(combined_output(stdout, stderr)).to_contain("All checks passed")
```

</details>

#### should accept host-owned semantic mutation in a host lane

- Check that semantic state mutation remains legal on the host lane
- "    fn is checked
- "var state = WidgetState
- "target later
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check that semantic state mutation remains legal on the host lane")
val source = host_gpu_fixture(
    "class WidgetState:\n" +
    "    checked: bool\n" +
    "    fn is_checked() -> bool: self.checked\n\n" +
    "var state = WidgetState(checked: false)\n" +
    "target.later() host \\:\n" +
    "    state.checked = true\n"
)

val (stdout, stderr, code) = check_source("host_semantic_mutation", source)

expect(code).to_equal(0)
expect(combined_output(stdout, stderr)).to_contain("All checks passed")
```

</details>

#### should accept GPU render and effect batching with packet bounds

- Check that GPU lane work is expressed as a coarse render/effect batch
- "packet target later
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check that GPU lane work is expressed as a coarse render/effect batch")
val source = host_gpu_fixture(
    "packet_target.later(max_packet: 4096) gpu \\:\n" +
    "    val render_batch = \"DrawIR:rect, glyph, image\"\n" +
    "    val effect_batch = \"blur, opacity, composite\"\n" +
    "    val batch_kind = render_batch + \" | \" + effect_batch\n"
)

val (stdout, stderr, code) = check_source("gpu_render_effect_batch", source)

expect(code).to_equal(0)
expect(combined_output(stdout, stderr)).to_contain("All checks passed")
```

</details>

#### should reject GPU semantic mutation with a diagnostic

- Validate that a GPU lane cannot commit host-owned semantic state
   - Expected: result.ok is false
   - Expected: result.estimated_ms equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate that a GPU lane cannot commit host-owned semantic state")
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    512,
    true,
    false,
    true,
    8
)

expect(result.ok).to_equal(false)
expect(result.diagnostic).to_contain("GPU lane cannot mutate host semantic state")
expect(result.estimated_ms).to_equal(8)
```

</details>

<details>
<summary>Advanced: should warn for per-widget GPU dispatch inside a loop</summary>

#### should warn for per-widget GPU dispatch inside a loop

- Validate that repeated widget-level GPU later calls are diagnosed
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate that repeated widget-level GPU later calls are diagnosed")
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    512,
    false,
    true,
    true,
    8
)

expect(result.ok).to_equal(false)
expect(result.diagnostic).to_contain("per-widget GPU dispatch")
```

</details>


</details>

#### should record faster strict GPU event-flow evidence

- Build event-flow evidence for host event to GPU Draw IR batch to present
   - Expected: evidence.ok is true
   - Expected: evidence.event_count equals `3`
   - Expected: evidence.draw_ir_delta_count equals `2`
   - Expected: evidence.event_to_present_ms equals `12`
   - Expected: evidence.candidate_frame_p50_ms equals `10`
   - Expected: evidence.candidate_frame_p95_ms equals `15`
   - Expected: evidence.speedup_x1000 equals `2000`
   - Expected: evidence.pixel_hash equals `1113616374`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build event-flow evidence for host event to GPU Draw IR batch to present")
val evidence = engine2d_host_gpu_event_flow_evidence(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    3,
    2,
    384,
    4096,
    false,
    false,
    true,
    4,
    6,
    10,
    20,
    30,
    1113616374,
    true
)

expect(evidence.ok).to_equal(true)
expect(evidence.event_count).to_equal(3)
expect(evidence.draw_ir_delta_count).to_equal(2)
expect(evidence.event_to_present_ms).to_equal(12)
expect(evidence.candidate_frame_p50_ms).to_equal(10)
expect(evidence.candidate_frame_p95_ms).to_equal(15)
expect(evidence.speedup_x1000).to_equal(2000)
expect(evidence.pixel_hash).to_equal(1113616374)
expect(engine2d_host_gpu_event_flow_summary(evidence)).to_contain("candidate_p50_ms=10")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/host_gpu_lane.md](doc/02_requirements/feature/host_gpu_lane.md)
- **Plan:** [doc/03_plan/sys_test/host_gpu_lane.md](doc/03_plan/sys_test/host_gpu_lane.md)
- **Design:** [doc/05_design/host_gpu_lane.md](doc/05_design/host_gpu_lane.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
