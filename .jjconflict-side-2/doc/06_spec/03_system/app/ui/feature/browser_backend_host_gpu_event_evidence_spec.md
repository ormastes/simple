# Browser Backend Host/GPU Event Evidence Spec

> System-level source and documentation evidence for BrowserBackend input-event host/GPU scheduling telemetry. The focused unit probe executes the runtime path; this system spec ensures the implementation, executable assertions, and generated manual stay connected.

<!-- sdn-diagram:id=browser_backend_host_gpu_event_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_backend_host_gpu_event_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_backend_host_gpu_event_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_backend_host_gpu_event_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

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
| Updated | 2026-06-01 |
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

- Inspect BrowserBackend implementation for event-flow telemetry fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should keep executable BrowserBackend assertions for input event flow

- Inspect the focused executable probe and unit spec for event-flow assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Inspect generated manuals for event-flow markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md](doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md)
- **Plan:** [doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md](doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
