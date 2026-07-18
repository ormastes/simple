# Shell Baremetal Backend Specification

> 1. var backend =  capture backend

<!-- sdn-diagram:id=shell_baremetal_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_baremetal_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_baremetal_backend_spec -> std
shell_baremetal_backend_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_baremetal_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Baremetal Backend Specification

## Scenarios

### baremetal shared WM backend contract

#### renders a live rich scene through CompositorBackend

1. var backend =  capture backend
   - Expected: backend.clear_count equals `1`
   - Expected: backend.fill_count > 0 is true
   - Expected: backend.text_count > 0 is true
   - Expected: backend.present_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = _capture_backend()
val window = simple_gui_internal_window(
    "surface-41", "41", 7001u64, "editor", "Live Editor",
    80, 70, 420, 300, "document=notes.spl", false, true, 0
)
val scene = simple_gui_internal_window_scene(800, 600, "simpleos-compositor", [window])
val pixels = _solid_pixels(412 * 264, 0xFF102030u32)
val frame = WmContentFrame(window_id: "41", scene_revision: 7, content_revision: 3, origin_kind: WM_CONTENT_ORIGIN_SIMPLE_WEB, width: 412, height: 264, pixels: pixels, checksum: wm_content_frame_checksum(pixels), parent_window_id: "", offset_x: 0, offset_y: 0)
render_baremetal_shared_wm_scene(backend, scene, empty_taskbar_model(), [frame], 7, 9, "12:34")

expect(backend.clear_count).to_equal(1)
expect(backend.fill_count > 0).to_be(true)
expect(backend.text_count > 0).to_be(true)
expect(backend.present_count).to_equal(0)
```

</details>

#### routes the production loop through authoritative runtime scene inputs

<details>
<summary>Executable SSpec</summary>

```simple
val src = file_read("src/os/desktop/shell.spl")
val run_start = src.index_of("me run_baremetal") ?? 0
val snapshot_start = src.index_of("fn runtime_scene_snapshot") ?? src.len()
val run_body = src.slice(run_start, snapshot_start)
expect(src).to_contain("me render_baremetal_frame(executor: Engine2dWmFrameExecutor)")
expect(src).to_contain("executor.render(scene, taskbar, content_frames")
expect(run_body).to_contain("self.render_baremetal_frame(executor)")
expect(run_body.contains("render_baremetal_shared_wm_scene")).to_be(false)
```

</details>

#### routes the live taskbar model and clock through shared taskbar object rendering

<details>
<summary>Executable SSpec</summary>

```simple
val src = file_read("src/os/desktop/shell_baremetal.spl")
expect(src).to_contain("shared_wm_scene_render_taskbar_context_to_backend")
expect(src).to_contain("SharedWmTaskbarRenderInput")
expect(src.contains("shared_wm_scene_render_to_backend_with_taskbar")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_baremetal_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- baremetal shared WM backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
