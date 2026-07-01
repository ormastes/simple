# SGTTI Compositor Adapter Spec

> Unit tests for the Simple Gui Texture Tree Interface (SGTTI) compositor adapter. Tests that compositor surfaces produce correct WinTextSnapshot nodes via `gtti_snapshot_from_compositor` with a real Compositor instance, and that hidden WM mode populates the tree without rendering.

<!-- sdn-diagram:id=gtti_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gtti_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gtti_spec -> std
gtti_spec -> os
gtti_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gtti_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SGTTI Compositor Adapter Spec

Unit tests for the Simple Gui Texture Tree Interface (SGTTI) compositor adapter. Tests that compositor surfaces produce correct WinTextSnapshot nodes via `gtti_snapshot_from_compositor` with a real Compositor instance, and that hidden WM mode populates the tree without rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/compositor/gtti_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for the Simple Gui Texture Tree Interface (SGTTI) compositor adapter.
Tests that compositor surfaces produce correct WinTextSnapshot nodes via
`gtti_snapshot_from_compositor` with a real Compositor instance, and that
hidden WM mode populates the tree without rendering.

## Scenarios

### WM mode constants

#### WM_MODE_HIDDEN is distinct from WM_MODE_NORMAL

1. assert true


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(WM_MODE_HIDDEN != WM_MODE_NORMAL)
```

</details>

#### wm_mode_is_hidden returns true for WM_MODE_HIDDEN

1. assert true


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(wm_mode_is_hidden(WM_MODE_HIDDEN))
```

</details>

#### wm_mode_is_hidden returns false for WM_MODE_NORMAL

1. assert false


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_false(wm_mode_is_hidden(WM_MODE_NORMAL))
```

</details>

### win_text_compositor_snapshot

#### empty surface list produces empty snapshot

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [GttiSurface] = []
val snap = win_text_compositor_snapshot(gtti_surfaces: empty, wm_mode: "hidden", captured_at_ms: 1000, max_age_ms: 5000, now_ms: 1000)
expect(snap.access.surfaces.len()).to_equal(0)
expect(snap.access.nodes.len()).to_equal(0)
expect(snap.sources.len()).to_equal(1)
expect(snap.sources[0].source_id).to_equal("compositor")
```

</details>

#### single surface produces one surface and one node

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GttiSurface(window_id: "1", title: "TestApp", x: 0, y: 0, width: 800, height: 600, visible: true, focused: true, app_id: "test_app")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs], wm_mode: "normal", captured_at_ms: 1000, max_age_ms: 5000, now_ms: 1000)
expect(snap.access.surfaces.len()).to_equal(1)
expect(snap.access.nodes.len()).to_equal(1)
expect(snap.access.surfaces[0].title).to_equal("TestApp")
expect(snap.access.surfaces[0].surface_id).to_equal("compositor:1")
```

</details>

#### node kind is compositor_window

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GttiSurface(window_id: "2", title: "Editor", x: 10, y: 20, width: 640, height: 480, visible: true, focused: false, app_id: "editor")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs], wm_mode: "hidden", captured_at_ms: 1000, max_age_ms: 5000, now_ms: 1000)
expect(snap.access.nodes[0].kind).to_equal("compositor_window")
expect(snap.access.nodes[0].text_value).to_equal("Editor")
```

</details>

#### source kind is simpleos_compositor

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GttiSurface(window_id: "3", title: "W", x: 0, y: 0, width: 100, height: 100, visible: true, focused: true, app_id: "")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs], wm_mode: "hidden", captured_at_ms: 500, max_age_ms: 5000, now_ms: 500)
expect(snap.sources[0].source_kind).to_equal("simpleos_compositor")
```

</details>

#### mode is compositor

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GttiSurface(window_id: "4", title: "W", x: 0, y: 0, width: 100, height: 100, visible: true, focused: true, app_id: "")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs], wm_mode: "normal", captured_at_ms: 500, max_age_ms: 5000, now_ms: 500)
expect(snap.access.mode).to_equal("compositor")
```

</details>

### hidden WM mode populates surface tree

#### hidden mode snapshot has surfaces

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs1 = GttiSurface(window_id: "10", title: "HiddenApp", x: 0, y: 0, width: 1024, height: 768, visible: true, focused: true, app_id: "hidden_app")
val gs2 = GttiSurface(window_id: "11", title: "Background", x: 100, y: 100, width: 400, height: 300, visible: false, focused: false, app_id: "bg")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs1, gs2], wm_mode: "hidden", captured_at_ms: 2000, max_age_ms: 5000, now_ms: 2000)
expect(snap.access.surfaces.len()).to_equal(2)
expect(snap.access.nodes.len()).to_equal(2)
```

</details>

#### hidden mode nodes carry wm_mode=hidden prop

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GttiSurface(window_id: "20", title: "HTest", x: 0, y: 0, width: 800, height: 600, visible: true, focused: true, app_id: "ht")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs], wm_mode: "hidden", captured_at_ms: 2000, max_age_ms: 5000, now_ms: 2000)
val node = snap.access.nodes[0]
var found_mode = ""
for prop in node.props:
    if prop.key == "wm_mode":
        found_mode = prop.value
expect(found_mode).to_equal("hidden")
```

</details>

#### hidden mode find returns compositor_window nodes by kind

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GttiSurface(window_id: "30", title: "FindMe", x: 0, y: 0, width: 640, height: 480, visible: true, focused: true, app_id: "finder")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs], wm_mode: "hidden", captured_at_ms: 3000, max_age_ms: 5000, now_ms: 3000)
val found = win_text_find_nodes(snap, "", "compositor_window", "", 10)
expect(found.len()).to_equal(1)
expect(found[0].text_value).to_equal("FindMe")
```

</details>

#### hidden mode find by text matches title

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs = GttiSurface(window_id: "31", title: "Calculator", x: 50, y: 50, width: 320, height: 240, visible: true, focused: true, app_id: "calc")
val snap = win_text_compositor_snapshot(gtti_surfaces: [gs], wm_mode: "hidden", captured_at_ms: 3000, max_age_ms: 5000, now_ms: 3000)
val found = win_text_find_nodes(snap, "", "", "Calculator", 10)
expect(found.len()).to_equal(1)
expect(found[0].kind).to_equal("compositor_window")
```

</details>

### compositor snapshot with multiple surfaces

#### three surfaces produce three nodes

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = GttiSurface(window_id: "40", title: "A", x: 0, y: 0, width: 100, height: 100, visible: true, focused: true, app_id: "a")
val b = GttiSurface(window_id: "41", title: "B", x: 100, y: 0, width: 100, height: 100, visible: true, focused: false, app_id: "b")
val c = GttiSurface(window_id: "42", title: "C", x: 200, y: 0, width: 100, height: 100, visible: false, focused: false, app_id: "c")
val snap = win_text_compositor_snapshot(gtti_surfaces: [a, b, c], wm_mode: "normal", captured_at_ms: 4000, max_age_ms: 5000, now_ms: 4000)
expect(snap.access.surfaces.len()).to_equal(3)
expect(snap.access.nodes.len()).to_equal(3)
```

</details>

#### active surface is first surface

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = GttiSurface(window_id: "50", title: "First", x: 0, y: 0, width: 100, height: 100, visible: true, focused: false, app_id: "f")
val b = GttiSurface(window_id: "51", title: "Second", x: 100, y: 0, width: 100, height: 100, visible: true, focused: true, app_id: "s")
val snap = win_text_compositor_snapshot(gtti_surfaces: [a, b], wm_mode: "normal", captured_at_ms: 5000, max_age_ms: 5000, now_ms: 5000)
expect(snap.access.active_surface).to_equal("compositor:50")
```

</details>

#### node visible prop matches surface visibility

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vis = GttiSurface(window_id: "60", title: "Vis", x: 0, y: 0, width: 100, height: 100, visible: true, focused: true, app_id: "v")
val hid = GttiSurface(window_id: "61", title: "Hid", x: 0, y: 0, width: 100, height: 100, visible: false, focused: false, app_id: "h")
val snap = win_text_compositor_snapshot(gtti_surfaces: [vis, hid], wm_mode: "hidden", captured_at_ms: 6000, max_age_ms: 5000, now_ms: 6000)
var vis_prop = ""
for prop in snap.access.nodes[0].props:
    if prop.key == "visible":
        vis_prop = prop.value
expect(vis_prop).to_equal("true")
var hid_prop = ""
for prop in snap.access.nodes[1].props:
    if prop.key == "visible":
        hid_prop = prop.value
expect(hid_prop).to_equal("false")
```

</details>

### gtti_snapshot_from_compositor with real Compositor

#### empty compositor produces empty snapshot

1. var comp =  make gtti test compositor
   - Expected: snap.access.surfaces.len() equals `0`
   - Expected: snap.access.nodes.len() equals `0`
   - Expected: snap.sources[0].source_id equals `compositor`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, 1000, 1000)
expect(snap.access.surfaces.len()).to_equal(0)
expect(snap.access.nodes.len()).to_equal(0)
expect(snap.sources[0].source_id).to_equal("compositor")
```

</details>

#### compositor with one window produces one compositor_window node

1. var comp =  make gtti test compositor

2. comp create window
   - Expected: snap.access.surfaces.len() equals `1`
   - Expected: snap.access.nodes.len() equals `1`
   - Expected: snap.access.nodes[0].kind equals `compositor_window`
   - Expected: snap.access.nodes[0].text_value equals `Terminal`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
comp.create_window("Terminal", 50, 50, 640, 480)
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, 2000, 2000)
expect(snap.access.surfaces.len()).to_equal(1)
expect(snap.access.nodes.len()).to_equal(1)
expect(snap.access.nodes[0].kind).to_equal("compositor_window")
expect(snap.access.nodes[0].text_value).to_equal("Terminal")
```

</details>

#### compositor with two windows produces two nodes

1. var comp =  make gtti test compositor

2. comp create window

3. comp create window
   - Expected: snap.access.surfaces.len() equals `2`
   - Expected: snap.access.nodes.len() equals `2`
   - Expected: snap.access.surfaces[0].title equals `Editor`
   - Expected: snap.access.surfaces[1].title equals `Browser`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
comp.create_window("Editor", 10, 10, 800, 600)
comp.create_window("Browser", 100, 100, 1024, 768)
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_NORMAL, 3000, 3000)
expect(snap.access.surfaces.len()).to_equal(2)
expect(snap.access.nodes.len()).to_equal(2)
expect(snap.access.surfaces[0].title).to_equal("Editor")
expect(snap.access.surfaces[1].title).to_equal("Browser")
```

</details>

#### focused window is marked focused in snapshot

1. var comp =  make gtti test compositor

2. comp focus window
   - Expected: found.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
val id1 = comp.create_window("Win1", 0, 0, 400, 300)
val id2 = comp.create_window("Win2", 50, 50, 400, 300)
comp.focus_window(id1)
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, 4000, 4000)
val found = win_text_find_nodes(snap, "", "compositor_window", "Win1", 10)
expect(found.len()).to_equal(1)
```

</details>

#### hidden mode label appears in node props

1. var comp =  make gtti test compositor

2. comp create window
   - Expected: found_mode equals `hidden`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
comp.create_window("HiddenTest", 0, 0, 320, 240)
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, 5000, 5000)
var found_mode = ""
for prop in snap.access.nodes[0].props:
    if prop.key == "wm_mode":
        found_mode = prop.value
expect(found_mode).to_equal("hidden")
```

</details>

#### normal mode label appears in node props

1. var comp =  make gtti test compositor

2. comp create window
   - Expected: found_mode equals `normal`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
comp.create_window("NormalTest", 0, 0, 320, 240)
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_NORMAL, 5000, 5000)
var found_mode = ""
for prop in snap.access.nodes[0].props:
    if prop.key == "wm_mode":
        found_mode = prop.value
expect(found_mode).to_equal("normal")
```

</details>

#### app_id is preserved from compositor surface

1. var comp =  make gtti test compositor

2. comp set window identity
   - Expected: snap.access.surfaces[0].app_id equals `my_app`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
val id = comp.create_window("MyApp", 0, 0, 640, 480)
comp.set_window_identity(id, 42, "my_app")
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, 6000, 6000)
expect(snap.access.surfaces[0].app_id).to_equal("my_app")
```

</details>

#### find by kind works on compositor adapter snapshot

1. var comp =  make gtti test compositor

2. comp create window
   - Expected: found.len() equals `1`
   - Expected: found[0].text_value equals `Findable`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
comp.create_window("Findable", 0, 0, 200, 150)
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, 7000, 7000)
val found = win_text_find_nodes(snap, "", "compositor_window", "", 10)
expect(found.len()).to_equal(1)
expect(found[0].text_value).to_equal("Findable")
```

</details>

#### find by title text works on compositor adapter snapshot

1. var comp =  make gtti test compositor

2. comp create window

3. comp create window
   - Expected: found.len() equals `1`
   - Expected: found[0].kind equals `compositor_window`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_gtti_test_compositor()
comp.create_window("Calculator", 100, 100, 320, 240)
comp.create_window("Settings", 200, 200, 400, 300)
val snap = gtti_snapshot_from_compositor(comp, WM_MODE_HIDDEN, 8000, 8000)
val found = win_text_find_nodes(snap, "", "", "Calculator", 10)
expect(found.len()).to_equal(1)
expect(found[0].kind).to_equal("compositor_window")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
