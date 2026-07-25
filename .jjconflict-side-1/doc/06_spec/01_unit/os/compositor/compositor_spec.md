# Compositor Specification

> <details>

<!-- sdn-diagram:id=compositor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compositor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compositor_spec -> std
compositor_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compositor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Specification

## Scenarios

### WindowSurface

#### constructs with all fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = WindowSurface(
    id: 1,
    title: "Test Window",
    x: 100,
    y: 50,
    width: 640,
    height: 480,
    visible: true,
    session: nil,
    dirty: false,
    owner_port: 0,
    process_id: 0,
    app_id: ""
)
expect(surface.id).to_equal(1)
expect(surface.title).to_equal("Test Window")
expect(surface.x).to_equal(100)
expect(surface.y).to_equal(50)
expect(surface.width).to_equal(640)
expect(surface.height).to_equal(480)
expect(surface.visible).to_equal(true)
expect(surface.dirty).to_equal(false)
```

</details>

#### has correct title

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = WindowSurface(
    id: 42,
    title: "My App",
    x: 0, y: 0,
    width: 800, height: 600,
    visible: true, session: nil, dirty: true,
    owner_port: 0,
    process_id: 0,
    app_id: ""
)
expect(surface.title).to_equal("My App")
```

</details>

#### supports dirty flag

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = WindowSurface(
    id: 1,
    title: "Dirty",
    x: 0, y: 0,
    width: 100, height: 100,
    visible: true, session: nil, dirty: true,
    owner_port: 0,
    process_id: 0,
    app_id: ""
)
expect(surface.dirty).to_equal(true)
```

</details>

### Compositor

#### when newly created

#### starts with empty surfaces

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = _make_test_compositor()
expect(comp.surfaces.len()).to_equal(0)
```

</details>

#### starts with focused_idx at -1

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = _make_test_compositor()
expect(comp.focused_idx).to_equal(-1)
```

</details>

#### starts with next_id at 1

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = _make_test_compositor()
expect(comp.next_id).to_equal(1)
```

</details>

#### starts not running

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = _make_test_compositor()
expect(comp.running).to_equal(false)
```

</details>

### Compositor create_window

#### returns window ID

1. var comp =  make test compositor
   - Expected: id equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("Test", 0, 0, 640, 480)
expect(id).to_equal(1)
```

</details>

#### adds surface to list

1. var comp =  make test compositor
   - Expected: comp.surfaces.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("Test", 0, 0, 640, 480)
expect(comp.surfaces.len()).to_equal(1)
```

</details>

#### increments next_id

1. var comp =  make test compositor
   - Expected: id1 equals `1`
   - Expected: id2 equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("Win1", 0, 0, 640, 480)
val id2 = comp.create_window("Win2", 100, 100, 640, 480)
expect(id1).to_equal(1)
expect(id2).to_equal(2)
```

</details>

#### creates multiple windows

1. var comp =  make test compositor
   - Expected: comp.surfaces.len() equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val _ = comp.create_window("A", 0, 0, 640, 480)
val _ = comp.create_window("B", 100, 0, 640, 480)
val _ = comp.create_window("C", 200, 0, 640, 480)
expect(comp.surfaces.len()).to_equal(3)
```

</details>

#### sets correct title on created surface

1. var comp =  make test compositor
   - Expected: comp.surfaces[0].title equals `My Window`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("My Window", 10, 20, 800, 600)
expect(comp.surfaces[0].title).to_equal("My Window")
```

</details>

#### sets correct position on created surface

1. var comp =  make test compositor
   - Expected: comp.surfaces[0].x equals `50`
   - Expected: comp.surfaces[0].y equals `75`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("Pos", 50, 75, 400, 300)
expect(comp.surfaces[0].x).to_equal(50)
expect(comp.surfaces[0].y).to_equal(75)
```

</details>

#### sets correct size on created surface

1. var comp =  make test compositor
   - Expected: comp.surfaces[0].width equals `1024`
   - Expected: comp.surfaces[0].height equals `768`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("Size", 0, 0, 1024, 768)
expect(comp.surfaces[0].width).to_equal(1024)
expect(comp.surfaces[0].height).to_equal(768)
```

</details>

#### creates visible window

1. var comp =  make test compositor
   - Expected: comp.surfaces[0].visible is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("Visible", 0, 0, 640, 480)
expect(comp.surfaces[0].visible).to_equal(true)
```

</details>

#### focuses newly created window

1. var comp =  make test compositor


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("Focus", 0, 0, 640, 480)
expect(comp.focused_idx).to_be_greater_than(-1)
```

</details>

### Compositor identity metadata

#### preserves process and app identity across window updates

1. var comp =  make test compositor

2. comp set window identity

3. comp move window
   - Expected: comp.window_process_id(id) equals `99`
   - Expected: comp.window_app_id(id) equals `app.identity`
   - Expected: comp.window_count_for_process(99) equals `1`
   - Expected: comp.windows_for_process(99).len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("Identity", 0, 0, 640, 480)
comp.set_window_identity(id, 99, "app.identity")
comp.move_window(id, 20, 30)
expect(comp.window_process_id(id)).to_equal(99)
expect(comp.window_app_id(id)).to_equal("app.identity")
expect(comp.window_count_for_process(99)).to_equal(1)
expect(comp.windows_for_process(99).len()).to_equal(1)
```

</details>

### Compositor destroy_window

#### removes window by ID

1. var comp =  make test compositor

2. comp destroy window
   - Expected: comp.surfaces.len() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id = comp.create_window("ToRemove", 0, 0, 640, 480)
comp.destroy_window(id)
expect(comp.surfaces.len()).to_equal(0)
```

</details>

#### does not remove other windows

1. var comp =  make test compositor

2. comp destroy window
   - Expected: comp.surfaces.len() equals `1`
   - Expected: comp.surfaces[0].title equals `Keep`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("Keep", 0, 0, 640, 480)
val id2 = comp.create_window("Remove", 100, 0, 640, 480)
comp.destroy_window(id2)
expect(comp.surfaces.len()).to_equal(1)
expect(comp.surfaces[0].title).to_equal("Keep")
```

</details>

#### handles destroying from list of three

1. var comp =  make test compositor

2. comp destroy window
   - Expected: comp.surfaces.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("A", 0, 0, 640, 480)
val id2 = comp.create_window("B", 100, 0, 640, 480)
val id3 = comp.create_window("C", 200, 0, 640, 480)
comp.destroy_window(id2)
expect(comp.surfaces.len()).to_equal(2)
```

</details>

### Compositor focus_window

#### updates focused_idx

1. var comp =  make test compositor

2. comp focus window
   - Expected: comp.surfaces[last_idx].id equals `id1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("A", 0, 0, 640, 480)
val id2 = comp.create_window("B", 100, 0, 640, 480)
comp.focus_window(id1)
# The focused window should be moved to front (last position in Z-order)
val last_idx = comp.surfaces.len() - 1
expect(comp.surfaces[last_idx].id).to_equal(id1)
```

</details>

#### brings focused window to front of Z-order

1. var comp =  make test compositor

2. comp focus window
   - Expected: last.id equals `id1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("Back", 0, 0, 640, 480)
val id2 = comp.create_window("Front", 100, 0, 640, 480)
# id2 is currently front; focus id1 should bring it to front
comp.focus_window(id1)
val last = comp.surfaces[comp.surfaces.len() - 1]
expect(last.id).to_equal(id1)
```

</details>

#### updates focused_idx to correct position

1. var comp =  make test compositor

2. comp focus window


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("A", 0, 0, 640, 480)
val id2 = comp.create_window("B", 100, 0, 640, 480)
comp.focus_window(id1)
expect(comp.focused_idx).to_be_greater_than(-1)
expect(comp.focused_idx).to_be_less_than(comp.surfaces.len())
```

</details>

### Compositor Z-order

#### new windows are added at end (front)

1. var comp =  make test compositor
   - Expected: last.id equals `id2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("Back", 0, 0, 640, 480)
val id2 = comp.create_window("Front", 100, 0, 640, 480)
val last = comp.surfaces[comp.surfaces.len() - 1]
expect(last.id).to_equal(id2)
```

</details>

#### first window is at index 0 (backmost)

1. var comp =  make test compositor
   - Expected: comp.surfaces[0].id equals `id1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val id1 = comp.create_window("First", 0, 0, 640, 480)
val id2 = comp.create_window("Second", 100, 0, 640, 480)
expect(comp.surfaces[0].id).to_equal(id1)
```

</details>

#### surfaces list length matches window count

1. var comp =  make test compositor
   - Expected: comp.surfaces.len() equals `0`
   - Expected: comp.surfaces.len() equals `1`
   - Expected: comp.surfaces.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
expect(comp.surfaces.len()).to_equal(0)
val _ = comp.create_window("A", 0, 0, 640, 480)
expect(comp.surfaces.len()).to_equal(1)
val _ = comp.create_window("B", 100, 0, 640, 480)
expect(comp.surfaces.len()).to_equal(2)
```

</details>

### Compositor cycle_focus

#### does nothing with single window

1. var comp =  make test compositor

2. comp cycle focus
   - Expected: comp.surfaces.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
val _ = comp.create_window("Only", 0, 0, 640, 480)
val before = comp.focused_idx
comp.cycle_focus()
# Should still be focused on the only window
expect(comp.surfaces.len()).to_equal(1)
```

</details>

#### does nothing with no windows

1. var comp =  make test compositor

2. comp cycle focus
   - Expected: comp.focused_idx equals `-1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var comp = _make_test_compositor()
comp.cycle_focus()
expect(comp.focused_idx).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/compositor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WindowSurface
- Compositor
- Compositor create_window
- Compositor identity metadata
- Compositor destroy_window
- Compositor focus_window
- Compositor Z-order
- Compositor cycle_focus

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
