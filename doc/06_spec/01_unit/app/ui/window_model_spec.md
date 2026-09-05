# Window Model Specification

> 1. var wm = new window manager

<!-- sdn-diagram:id=window_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_model_spec -> std
window_model_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Model Specification

## Scenarios

### shared UI window model

#### opens and replaces MDI window descriptors by id

1. var wm = new window manager

2. wm open window
   - Expected: wm.count() equals `1`
   - Expected: opened.title equals `Terminal`
   - Expected: false is true

3. wm open window
   - Expected: wm.count() equals `1`
   - Expected: replaced.title equals `Terminal 2`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wm = new_window_manager()

wm.open_window("terminal", "Terminal", 10, 20, 300, 200, _tree("one"))
expect(wm.count()).to_equal(1)
if val opened = wm.find("terminal"):
    expect(opened.title).to_equal("Terminal")
else:
    expect(false).to_equal(true)

wm.open_window("terminal", "Terminal 2", 30, 40, 320, 240, _tree("two"))
expect(wm.count()).to_equal(1)
if val replaced = wm.find("terminal"):
    expect(replaced.title).to_equal("Terminal 2")
else:
    expect(false).to_equal(true)
```

</details>

#### closes MDI window descriptors

1. var wm = new window manager

2. wm open window

3. wm close window
   - Expected: wm.count() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wm = new_window_manager()
wm.open_window("files", "Files", 0, 0, 400, 300, _tree("files"))

wm.close_window("files")

expect(wm.count()).to_equal(0)
expect(wm.find("files")).to_be_nil()
```

</details>

#### opens host HTML descriptors without requiring a UITree

1. var wm = new window manager

2. wm open info
   - Expected: wm.count() equals `1`
   - Expected: opened.html equals `<iframe></iframe>`
   - Expected: false is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wm = new_window_manager()
val descriptor = window_info("browser", "Browser", "<iframe></iframe>", 20, 30, 640, 480)

wm.open_info(descriptor)

expect(wm.count()).to_equal(1)
if val opened = wm.find("browser"):
    expect(opened.html).to_equal("<iframe></iframe>")
else:
    expect(false).to_equal(true)
```

</details>

#### tracks the active backend for shared MDI hosts

1. var electron wm = new window manager for backend

2. var tauri wm = new window manager for backend

3. var typo wm = new window manager for backend

4. var simple wm = new window manager
   - Expected: electron_wm.current_backend() equals `electron`
   - Expected: tauri_wm.current_backend() equals `tauri`
   - Expected: typo_wm.current_backend() equals `electron`
   - Expected: simple_wm.current_backend() equals `simple`
   - Expected: normalize_window_backend("unknown") equals `simple`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var electron_wm = new_window_manager_for_backend("electron")
var tauri_wm = new_window_manager_for_backend("tauri")
var typo_wm = new_window_manager_for_backend("election")
var simple_wm = new_window_manager()

expect(electron_wm.current_backend()).to_equal("electron")
expect(tauri_wm.current_backend()).to_equal("tauri")
expect(typo_wm.current_backend()).to_equal("electron")
expect(simple_wm.current_backend()).to_equal("simple")
expect(normalize_window_backend("unknown")).to_equal("simple")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/window_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared UI window model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
