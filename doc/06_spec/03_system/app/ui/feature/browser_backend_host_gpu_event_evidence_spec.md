# Browser Backend Host/GPU Event Evidence Spec

> System-level source and documentation evidence for BrowserBackend input-event host/GPU scheduling telemetry. The focused unit probe executes the runtime path; this system spec ensures the implementation, executable assertions, and generated manual stay connected.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Backend Host/GPU Event Evidence Spec

System-level source and documentation evidence for BrowserBackend input-event host/GPU scheduling telemetry. The focused unit probe executes the runtime path; this system spec ensures the implementation, executable assertions, and generated manual stay connected.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System-level source and documentation evidence for BrowserBackend input-event
host/GPU scheduling telemetry. The focused unit probe executes the runtime path;
this system spec ensures the implementation, executable assertions, and
generated manual stay connected.

**Requirements:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md
**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md
**Design:** doc/04_architecture/ui/simple_gui_stack.md
**Research:** N/A

## Acceptance

- BrowserBackend dispatch records host/GPU scheduling evidence from the input
  event envelope.
- The focused executable BrowserBackend runtime queue spec asserts enqueue,
  poll, dispatch, forward, backward, and render-roundtrip evidence.
- The generated manual exposes the same event-flow markers.

## Syntax

The BrowserBackend host input path must keep this order:

```simple
backend.push_event(event)
use std.spec.step

val events = backend.poll_events()
backend.record_event_dispatch(events[0])
backend.render_frame(tree, state)
```

`record_event_dispatch` may report host/GPU scheduling evidence, but it must not
be documented as a live runtime queue submit until it is tied to an actual
runtime packet and backend readback receipt.

## Examples

The focused BrowserBackend runtime queue probe prints:

```text
event_host_gpu_forwarded=true
event_host_gpu_backward_completed=false
event_roundtrip_status=rendered
```

## Scenarios

### BrowserBackend host GPU event evidence

#### should keep implementation telemetry tied to host GPU event-flow evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should keep implementation telemetry tied to host GPU event-flow evidence
- Inspect BrowserBackend implementation for event-flow telemetry fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep implementation telemetry tied to host GPU event-flow evidence")
step("Inspect BrowserBackend implementation for event-flow telemetry fields")
val source = rt_file_read_text("src/app/ui.browser/backend.spl")

expect(source).to_contain("last_input_event_host_gpu_target_lane: text")
expect(source).to_contain("last_input_event_host_gpu_forwarded: bool")
expect(source).to_contain("last_input_event_host_gpu_backward_completed: bool")
expect(source).to_contain("last_input_event_host_gpu_summary: text")
expect(source).to_contain("engine2d_host_gpu_draw_ir_event_flow(")
expect(source).to_contain("engine2d_host_gpu_draw_ir_event_flow_summary(flow)")
expect(source).to_contain("queued local browser event")
```

</details>

#### should route the live GPU-offload dispatch through the SOSIX seal gate when flagged (#39 Gap #2)

- should route the live GPU-offload dispatch through the SOSIX seal gate when flagged (#39 Gap #2)
- Inspect BrowserBackend dispatch for the flag-gated seal-before-share wiring


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route the live GPU-offload dispatch through the SOSIX seal gate when flagged (#39 Gap #2)")
step("Inspect BrowserBackend dispatch for the flag-gated seal-before-share wiring")
val source = rt_file_read_text("src/app/ui.browser/backend.spl")

# The seal is wired at the real dispatch site (browser_backend_dispatch_prepared_draw_ir),
# flag-gated + byte-preserving (draw_ir_payload_read(sealed) == payload.payload_sdn), so the
# dispatched bytes and rendered pixels are unchanged. Proven correct by the seal's identity
# property (sealed_draw_ir_payload_spec) + the routing proof (sosix_gpu_lane_route_spec, nogc twin).
expect(source).to_contain("if engine2d_sosix_gpu_lane_enabled():")
expect(source).to_contain("engine2d_host_gpu_seal_draw_ir_payload(payload.payload_sdn)")
expect(source).to_contain("draw_ir_payload_read(sealed)")
```

</details>

#### should keep executable BrowserBackend assertions for input event flow

- should keep executable BrowserBackend assertions for input event flow
- Inspect the focused executable probe and unit spec for event-flow assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep executable BrowserBackend assertions for input event flow")
step("Inspect the focused executable probe and unit spec for event-flow assertions")
val probe = rt_file_read_text("test/01_unit/app/ui/browser_backend_runtime_queue_probe.spl")
val spec = rt_file_read_text("test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl")

expect(probe).to_contain("backend.push_event(input_event)")
expect(probe).to_contain("backend.poll_events()")
expect(probe).to_contain("backend.record_event_dispatch(queued_events[0])")
expect(probe).to_contain("first_event_correlation_status=")
expect(probe).to_contain("first_event_correlation_summary=")
expect(probe).to_contain("event_host_gpu_forwarded=")
expect(probe).to_contain("event_host_gpu_backward_completed=")
expect(spec).to_contain("event_roundtrip_status=rendered")
expect(spec).to_contain("first_event_correlation_status=event_frame_readback_correlated")
expect(spec).to_contain("first_event_correlation_id=browser-input-1")
expect(spec).to_contain("event_enqueued_count=1")
expect(spec).to_contain("event_polled_count=1")
expect(spec).to_contain("event_dispatched_count=1")
expect(spec).to_contain("event_host_gpu_forwarded=true")
expect(spec).to_contain("event_host_gpu_backward_completed=false")
expect(spec).to_contain("backward_completed=false")
```

</details>

#### should keep generated manual evidence for BrowserBackend event flow

- should keep generated manual evidence for BrowserBackend event flow
- Inspect generated manuals for event-flow markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep generated manual evidence for BrowserBackend event flow")
step("Inspect generated manuals for event-flow markers")
expect(_marker_state(
    "doc/06_spec/test/01_unit/app/ui/browser_backend_runtime_queue_spec.md",
    "event_host_gpu_forwarded=true"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/test/01_unit/app/ui/browser_backend_runtime_queue_spec.md",
    "event_host_gpu_backward_completed=false"
)).to_equal("present")
expect(_marker_state(
    "doc/06_spec/test/01_unit/app/ui/browser_backend_runtime_queue_spec.md",
    "first_event_correlation_status=event_frame_readback_correlated"
)).to_equal("present")
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

- **Requirements:** `doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md`
- **Plan:** `doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md`
- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9bf1f03c0f14d0fd5ad9d3169ac3c88f1605c38579477b29ae6339129bc69be1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9bf1f03c0f14d0fd5ad9d3169ac3c88f1605c38579477b29ae6339129bc69be1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9bf1f03c0f14d0fd5ad9d3169ac3c88f1605c38579477b29ae6339129bc69be1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl
mirror: doc/06_spec/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep implementation telemetry tied to host GPU event-flow evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep implementation telemetry tied to host GPU event-flow evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route the live GPU-offload dispatch through the SOSIX seal gate when flagged (#39 Gap #2)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route the live GPU-offload dispatch through the SOSIX seal gate when flagged (#39 Gap #2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl:99:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep executable BrowserBackend assertions for input event flow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep executable BrowserBackend assertions for input event flow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/browser_backend_host_gpu_event_evidence_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep generated manual evidence for BrowserBackend event flow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
