# Browser Host Event Roundtrip Specification

> <details>

<!-- sdn-diagram:id=browser_host_event_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_host_event_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_host_event_roundtrip_spec -> std
browser_host_event_roundtrip_spec -> common
browser_host_event_roundtrip_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_host_event_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

> **Current execution: BLOCKED.** The installed pure-Simple runner accepts the
> source but fails before any example executes with `runtime error: field
> access on nil receiver`. No runtime PASS is claimed.

<details>
<summary>Full Scenario Manual</summary>

# Browser Host Event Roundtrip Specification

## Scenarios

### BrowserBackend host event roundtrip

#### should preserve one immutable frame identity across an input batch and reject foreign stale or replayed events

- Submit one session-owned Draw IR frame.
- Stamp move, down, up, and an unconsumed stale event with its session nonce,
  submission revision, composition, and scene.
- Accept move/down/up on revision 1, reject the exact repeated down event, and
  keep the frame valid for the following up event.
- Reject a foreign-session event and the unconsumed revision-1 event after
  revision 2 is submitted.

#### correlates a queued input event with a GPU frame dispatch receipt

- rt host gpu queue reset
- text widget
- button
- backend push event
- backend record event dispatch
- backend render frame
   - Expected: backend.input_event_enqueued_count equals `1`
   - Expected: backend.input_event_polled_count equals `1`
   - Expected: backend.input_event_dispatched_count equals `1`
   - Expected: backend.last_input_event_roundtrip_status equals `rendered`
   - Expected: backend.last_artifact_queue_dispatch_status equals `dispatched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_host_gpu_queue_reset()
val root = panel("browser_queue_root", "Browser Queue", [
    text_widget("browser_queue_copy", "Queued frame"),
    button("browser_queue_action", "Run", "run")
])
val tree = build_tree_with_title(root, "Browser Queue", "dark")
val state = init_state(tree)
val backend = BrowserBackend.create(64, 48, "vulkan").unwrap()

backend.push_event(UIEvent.Action("run"))
val queued_events = backend.poll_events()
expect(queued_events.len()).to_be_greater_than(0)
backend.record_event_dispatch(queued_events[0])
backend.render_frame(state.tree, state)

expect(backend.input_event_enqueued_count).to_equal(1)
expect(backend.input_event_polled_count).to_equal(1)
expect(backend.input_event_dispatched_count).to_equal(1)
expect(backend.last_input_event_roundtrip_status).to_equal("rendered")
expect(backend.last_input_event_host_gpu_forwarded).to_be(true)
expect(backend.last_input_event_host_gpu_backward_completed).to_be(true)
expect(backend.last_artifact_queue_dispatch_status).to_equal("dispatched")
expect(backend.last_artifact_queue_backend_handle).to_be_greater_than(0)
```

</details>

#### routes BrowserApp host input through the queued receipt before session dispatch

- Submit one production BrowserApp Draw IR frame.
- Deliver pointer move, down, and up through `BrowserBackend.push_event` and
  `poll_events`.
- Require all three dispatch receipts while the UISession submission revision
  and composition identity remain unchanged.

<details>
<summary>Executable SSpec</summary>

```simple
val submitted = app.session.submit_widget_draw_ir(672, 448, DRAW_IR_BACKEND_GPU)
app.handle_ui_event(UIEvent.MouseEvent(x: 10.0, y: 20.0, button: "", kind: "move"))
app.handle_ui_event(UIEvent.MouseEvent(x: 10.0, y: 20.0, button: "left", kind: "down"))
app.handle_ui_event(UIEvent.MouseEvent(x: 10.0, y: 20.0, button: "left", kind: "up"))
expect(app.session.draw_ir_submission_revision).to_equal(1)
expect(app.session.submitted_draw_ir_composition_id).to_equal(submitted.composition_id)
expect(app.backend.input_event_dispatched_count).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | BLOCKED — no examples executed |
| Source | `test/01_unit/app/ui/browser_host_event_roundtrip_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserBackend host event roundtrip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
