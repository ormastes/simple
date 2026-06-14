# Browser Backend Runtime Queue Spec

> This focused spec proves a GPU-selected BrowserBackend frame surfaces host/GPU runtime queue submit and drain provenance on the backend API. Cache-hit behavior is explicit: an unchanged cached frame reports that no new runtime queue request was made instead of leaving stale queue receipts visible.

<!-- sdn-diagram:id=browser_backend_runtime_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_backend_runtime_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_backend_runtime_queue_spec -> std
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
packet plus a same-frame backend readback receipt and nonblank/nonuniform pixel
oracle, then renders the same frame again and asserts that the cache hit
reports `not_requested` queue/readback status instead of stale receipt data.

## Scenarios

### browser backend runtime queue provenance

#### surfaces queue evidence on GPU frames and resets it on cached frames

- First GPU-selected render emits and drains one runtime queue packet
   - Expected: code equals `0`
- Second unchanged frame is served from cache and reports no queue or readback request


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("./bin/simple", ["run", "test/01_unit/app/ui/browser_backend_runtime_queue_probe.spl"])
val output = stdout + stderr

step("First GPU-selected render emits and drains one runtime queue packet")
expect(code).to_equal(0)
expect(output).to_contain("backend=vulkan")
expect(output).to_contain("first_pixel_count=3072")
expect(output).to_contain("first_checksum=772887022")
expect(output).to_contain("first_nonuniform_count=2884")
expect(output).to_contain("first_submit=submitted")
expect(output).to_contain("first_drain=drained")
expect(output).to_contain("first_packet=1")
expect(output).to_contain("first_drained=1")
expect(output).to_contain("first_backend_handle=0")
expect(output).to_contain("first_reason=drained runtime queue")
expect(output).to_contain("first_readback_status=readback")
expect(output).to_contain("first_readback_backend=vulkan")
expect(output).to_contain("first_readback_pixel_count=3072")
expect(output).to_contain("first_readback_reason=same-frame Engine2D read_pixels")
expect(output).to_contain("first_gpu_readback_source=device_readback")

step("Second unchanged frame is served from cache and reports no queue or readback request")
expect(output).to_contain("second_fast_hits=1")
expect(output).to_contain("second_submit=not_requested")
expect(output).to_contain("second_drain=not_requested")
expect(output).to_contain("second_packet=0")
expect(output).to_contain("second_drained=0")
expect(output).to_contain("second_backend_handle=0")
expect(output).to_contain("second_reason=runtime queue not requested")
expect(output).to_contain("second_readback_status=not_requested")
expect(output).to_contain("second_readback_pixel_count=0")
expect(output).to_contain("second_readback_checksum=0")
expect(output).to_contain("second_gpu_readback_source=not_requested")
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
