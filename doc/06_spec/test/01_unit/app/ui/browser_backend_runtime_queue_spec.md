# Browser Backend Runtime Queue Spec

> This focused spec proves a GPU-selected BrowserBackend frame surfaces host/GPU runtime queue submit and drain provenance on the backend API. Cache-hit behavior is explicit: an unchanged cached frame reports that no new runtime queue request was made instead of leaving stale queue receipts visible.

<!-- sdn-diagram:id=browser_backend_runtime_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_backend_runtime_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_backend_runtime_queue_spec -> std
browser_backend_runtime_queue_spec -> common
browser_backend_runtime_queue_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_backend_runtime_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Backend Runtime Queue Spec

This focused spec proves a GPU-selected BrowserBackend frame surfaces host/GPU runtime queue submit and drain provenance on the backend API. Cache-hit behavior is explicit: an unchanged cached frame reports that no new runtime queue request was made instead of leaving stale queue receipts visible.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused spec proves a GPU-selected BrowserBackend frame surfaces
host/GPU runtime queue submit and drain provenance on the backend API.
Cache-hit behavior is explicit: an unchanged cached frame reports that no new
runtime queue request was made instead of leaving stale queue receipts visible.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

The scenario renders a static BrowserBackend frame with the Vulkan backend,
asserts that the first frame reports one submitted and drained runtime queue
packet, then renders the same frame again and asserts that the cache hit reports
`not_requested` queue status instead of stale receipt data.

## Scenarios

### browser backend runtime queue provenance

#### surfaces queue evidence on GPU frames and resets it on cached frames

- rt host gpu queue reset
- Err
   - Expected: e equals ``
- Ok
- First GPU-selected render emits and drains one runtime queue packet
- backend render frame
   - Expected: backend.gpu_backend() equals `vulkan`
   - Expected: backend.last_artifact_queue_submit_status equals `WEB_RENDER_QUEUE_STATUS_SUBMITTED`
   - Expected: backend.last_artifact_queue_drain_status equals `WEB_RENDER_QUEUE_STATUS_DRAINED`
   - Expected: backend.last_artifact_queue_drained equals `1`
- Second unchanged frame is served from cache and reports no queue request
- backend render frame
   - Expected: backend.static_frame_fast_hits equals `1`
   - Expected: backend.last_artifact_queue_submit_status equals `WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED`
   - Expected: backend.last_artifact_queue_drain_status equals `WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED`
   - Expected: backend.last_artifact_queue_packet_id equals `0`
   - Expected: backend.last_artifact_queue_drained equals `0`
   - Expected: backend.last_artifact_queue_reason equals `runtime queue not requested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_host_gpu_queue_reset()
val state = runtime_queue_browser_state()
val backend_result = BrowserBackend.create(64, 48, "vulkan")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        step("First GPU-selected render emits and drains one runtime queue packet")
        backend.render_frame(state.tree, state)
        expect(backend.gpu_backend()).to_equal("vulkan")
        expect(backend.last_artifact_queue_submit_status).to_equal(WEB_RENDER_QUEUE_STATUS_SUBMITTED)
        expect(backend.last_artifact_queue_drain_status).to_equal(WEB_RENDER_QUEUE_STATUS_DRAINED)
        expect(backend.last_artifact_queue_packet_id).to_be_greater_than(0)
        expect(backend.last_artifact_queue_drained).to_equal(1)
        expect(backend.last_artifact_queue_reason).to_contain("drained runtime queue")

        step("Second unchanged frame is served from cache and reports no queue request")
        backend.render_frame(state.tree, state)
        expect(backend.static_frame_fast_hits).to_equal(1)
        expect(backend.last_artifact_queue_submit_status).to_equal(WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED)
        expect(backend.last_artifact_queue_drain_status).to_equal(WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED)
        expect(backend.last_artifact_queue_packet_id).to_equal(0)
        expect(backend.last_artifact_queue_drained).to_equal(0)
        expect(backend.last_artifact_queue_reason).to_equal("runtime queue not requested")
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

- **Plan:** [doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md](doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
