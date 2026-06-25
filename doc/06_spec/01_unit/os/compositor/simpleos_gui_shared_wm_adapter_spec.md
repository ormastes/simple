# SimpleOS GUI Shared WM Adapter Spec

> Focused proof that the SimpleOS GUI adapter uses the shared WM bridge,

<!-- sdn-diagram:id=simpleos_gui_shared_wm_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_gui_shared_wm_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_gui_shared_wm_adapter_spec -> std
simpleos_gui_shared_wm_adapter_spec -> common
simpleos_gui_shared_wm_adapter_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_gui_shared_wm_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS GUI Shared WM Adapter Spec

Focused proof that the SimpleOS GUI adapter uses the shared WM bridge,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Focused proof that the SimpleOS GUI adapter uses the shared WM bridge,
input, and framebuffer render path instead of only reporting capability names.

## Scenarios

### SimpleOS GUI adapter shared WM proof

#### routes bridge, input, and framebuffer presentation through HostCompositor

1. adapter deliver bridge request
2. adapter render framebuffer frame
   - Expected: simpleos_gui_adapter_display_path_name(adapter) equals `simpleos-framebuffer`
   - Expected: simpleos_gui_adapter_content_renderer_name(adapter) equals `simple_web`
   - Expected: adapter.delivered_bridge_events equals `1`
   - Expected: adapter.presented_frames equals `1`
   - Expected: adapter.compositor.windows.len() equals `1`
   - Expected: adapter.compositor.windows[0].content equals `adapter-ready`
   - Expected: _adapter_present_count equals `1`
   - Expected: _adapter_clear_color equals `0xFF0F172Au32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_adapter_present_count = 0
_adapter_chrome_fill_count = 0
_adapter_clear_color = 0u32
val backend = AdapterCaptureBackend(w: 240, h: 180)
val adapter = SimpleOsGuiAdapter.new(backend, Size.wh(240, 180))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 24, 36, 128, 92, "adapter-ready", 800, "/sys/apps/terminal")
adapter.render_framebuffer_frame()

expect(simpleos_gui_adapter_display_path_name(adapter)).to_equal("simpleos-framebuffer")
expect(simpleos_gui_adapter_content_renderer_name(adapter)).to_equal("simple_web")
expect(adapter.delivered_bridge_events).to_equal(1)
expect(adapter.presented_frames).to_equal(1)
expect(adapter.compositor.windows.len()).to_equal(1)
expect(adapter.compositor.windows[0].content).to_equal("adapter-ready")
expect(_adapter_present_count).to_equal(1)
expect(_adapter_chrome_fill_count).to_be_greater_than(0)
expect(_adapter_clear_color).to_equal(0xFF0F172Au32)
```

</details>

#### applies bridge lifecycle actions through the shared host compositor path

1. adapter deliver bridge request
2. adapter deliver bridge request
3. adapter deliver bridge request
   - Expected: adapter.compositor.windows[0].x equals `48`
   - Expected: adapter.compositor.windows[0].y equals `52`
   - Expected: adapter.compositor.windows[0].w equals `144`
   - Expected: adapter.compositor.windows[0].h equals `104`
4. adapter deliver bridge request
   - Expected: adapter.compositor.windows[0].minimized is true
5. adapter deliver bridge request
   - Expected: adapter.compositor.windows[0].minimized is false
   - Expected: adapter.compositor.windows[0].focused is true
   - Expected: adapter.delivered_bridge_events equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = AdapterCaptureBackend(w: 240, h: 180)
val adapter = SimpleOsGuiAdapter.new(backend, Size.wh(240, 180))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 24, 36, 128, 92, "adapter-ready", 800, "/sys/apps/terminal")
val wid = adapter.compositor.windows[0].id

adapter.deliver_bridge_request(2, 44, COMP_MOVE.to_i64(), wid, "", 48, 52, 0, 0, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(3, 44, COMP_RESIZE.to_i64(), wid, "", 0, 0, 144, 104, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].x).to_equal(48)
expect(adapter.compositor.windows[0].y).to_equal(52)
expect(adapter.compositor.windows[0].w).to_equal(144)
expect(adapter.compositor.windows[0].h).to_equal(104)

adapter.deliver_bridge_request(4, 44, COMP_MINIMIZE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].minimized).to_equal(true)

adapter.deliver_bridge_request(5, 44, COMP_RESTORE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].minimized).to_equal(false)
expect(adapter.compositor.windows[0].focused).to_equal(true)
expect(adapter.delivered_bridge_events).to_equal(5)
```

</details>

#### applies title focus maximize update and destroy through the adapter bridge

1. adapter deliver bridge request
2. adapter deliver bridge request
3. adapter deliver bridge request
   - Expected: adapter.compositor.windows[0].title equals `Terminal Renamed`
4. adapter deliver bridge request
   - Expected: adapter.compositor.windows[1].id equals `first_id`
   - Expected: adapter.compositor.windows[1].focused is true
   - Expected: adapter.compositor.windows[0].id equals `second_id`
   - Expected: adapter.compositor.windows[0].focused is false
5. adapter deliver bridge request
   - Expected: adapter.compositor.windows[1].x equals `0`
   - Expected: adapter.compositor.windows[1].y equals `48`
   - Expected: adapter.compositor.windows[1].w equals `320`
   - Expected: adapter.compositor.windows[1].h equals `144`
6. adapter deliver bridge request
   - Expected: adapter.compositor.windows[1].content equals `updated-content`
7. adapter deliver bridge request
   - Expected: adapter.compositor.windows.len() equals `1`
   - Expected: adapter.compositor.windows[0].id equals `second_id`
   - Expected: adapter.delivered_bridge_events equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = AdapterCaptureBackend(w: 320, h: 240)
val adapter = SimpleOsGuiAdapter.new(backend, Size.wh(320, 240))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 24, 36, 128, 92, "adapter-ready", 800, "/sys/apps/terminal")
adapter.deliver_bridge_request(2, 55, COMP_CREATE_WINDOW.to_i64(), 0, "Editor", 64, 76, 150, 120, "editor-ready", 801, "/sys/apps/editor")
val first_id = adapter.compositor.windows[0].id
val second_id = adapter.compositor.windows[1].id

adapter.deliver_bridge_request(3, 44, COMP_SET_TITLE.to_i64(), first_id, "Terminal Renamed", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].title).to_equal("Terminal Renamed")

adapter.deliver_bridge_request(4, 44, COMP_FOCUS.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[1].id).to_equal(first_id)
expect(adapter.compositor.windows[1].focused).to_equal(true)
expect(adapter.compositor.windows[0].id).to_equal(second_id)
expect(adapter.compositor.windows[0].focused).to_equal(false)

adapter.deliver_bridge_request(5, 44, COMP_MAXIMIZE.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[1].x).to_equal(0)
expect(adapter.compositor.windows[1].y).to_equal(48)
expect(adapter.compositor.windows[1].w).to_equal(320)
expect(adapter.compositor.windows[1].h).to_equal(144)

adapter.deliver_bridge_request(6, 44, COMP_UPDATE_TREE.to_i64(), first_id, "", 0, 0, 0, 0, "updated-content", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[1].content).to_equal("updated-content")

adapter.deliver_bridge_request(7, 44, COMP_DESTROY_WINDOW.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows.len()).to_equal(1)
expect(adapter.compositor.windows[0].id).to_equal(second_id)
expect(adapter.delivered_bridge_events).to_equal(7)
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


</details>
