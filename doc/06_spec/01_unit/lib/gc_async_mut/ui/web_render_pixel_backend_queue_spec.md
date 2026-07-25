# Web Render Pixel Backend Runtime Queue Spec

> This focused spec proves the shared WebRenderArtifact boundary carries host/GPU runtime queue submit and drain provenance for GPU-backed web pixel artifacts. BrowserBackend mirrors these fields from the artifact after `render_frame`.

<!-- sdn-diagram:id=web_render_pixel_backend_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_render_pixel_backend_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_render_pixel_backend_queue_spec -> std
web_render_pixel_backend_queue_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_render_pixel_backend_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Render Pixel Backend Runtime Queue Spec

This focused spec proves the shared WebRenderArtifact boundary carries host/GPU runtime queue submit and drain provenance for GPU-backed web pixel artifacts. BrowserBackend mirrors these fields from the artifact after `render_frame`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused spec proves the shared WebRenderArtifact boundary carries
host/GPU runtime queue submit and drain provenance for GPU-backed web pixel
artifacts. BrowserBackend mirrors these fields from the artifact after
`render_frame`.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

The GPU scenario renders a tiny HTML fixture through the Vulkan-selected
Engine2D pixel backend, then asserts that the `WebRenderArtifact` records a
submitted packet, one drained packet, and the runtime backend handle. The
software scenario asserts the same artifact fields remain queue-neutral.

## Scenarios

### web render pixel backend runtime queue provenance

#### rejects an invalid Draw IR viewport before Engine2D creation

The shared composition artifact helper rejects a zero viewport with empty
pixels, unavailable Engine2D status, and no runtime queue submission.

#### preserves the executor readback source without fabricating queue dispatch

A software Draw IR rectangle retains `cpu_mirror` readback provenance and a
64-pixel result while queue submit and dispatch remain `not_requested`.

#### stamps GPU web render artifacts with runtime queue submit and drain evidence

- rt host gpu queue reset
   - Expected: artifact.engine2d_backend equals `vulkan`
   - Expected: artifact.queue_submit_status equals `submitted`
   - Expected: artifact.queue_drain_status equals `WEB_RENDER_QUEUE_STATUS_DRAINED`
   - Expected: artifact.queue_packet_id equals `1`
   - Expected: artifact.queue_drained equals `1`
   - Expected: artifact.queue_backend_handle equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_host_gpu_queue_reset()
val req = web_render_adapter_request(WEB_RENDER_TARGET_PURE_SIMPLE, "surface", "Queue", "<main><p>queued</p></main>", "", "", 64, 48).with_pixel_output()
val artifact = web_render_html_request_to_pixel_artifact_with_backend(req, "<html><body><main><p>queued</p></main></body></html>", "vulkan")

expect(artifact.engine2d_backend).to_equal("vulkan")
expect(artifact.queue_submit_status).to_equal("submitted")
expect(artifact.queue_drain_status).to_equal(WEB_RENDER_QUEUE_STATUS_DRAINED)
expect(artifact.queue_packet_id).to_equal(1)
expect(artifact.queue_drained).to_equal(1)
expect(artifact.queue_backend_handle).to_equal(7)
expect(artifact.queue_reason).to_contain("drained runtime queue")
```

</details>

#### keeps software web render artifacts queue-neutral

- rt host gpu queue reset
   - Expected: artifact.engine2d_backend equals `software`
   - Expected: artifact.queue_submit_status equals `WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED`
   - Expected: artifact.queue_drain_status equals `WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED`
   - Expected: artifact.queue_packet_id equals `0`
   - Expected: artifact.queue_drained equals `0`
   - Expected: artifact.queue_backend_handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_host_gpu_queue_reset()
val req = web_render_adapter_request(WEB_RENDER_TARGET_PURE_SIMPLE, "surface", "Queue", "<main><p>host</p></main>", "", "", 64, 48).with_pixel_output()
val artifact = web_render_html_request_to_pixel_artifact_with_backend(req, "<html><body><main><p>host</p></main></body></html>", "software")

expect(artifact.engine2d_backend).to_equal("software")
expect(artifact.queue_submit_status).to_equal(WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED)
expect(artifact.queue_drain_status).to_equal(WEB_RENDER_QUEUE_STATUS_NOT_REQUESTED)
expect(artifact.queue_packet_id).to_equal(0)
expect(artifact.queue_drained).to_equal(0)
expect(artifact.queue_backend_handle).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md](doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
