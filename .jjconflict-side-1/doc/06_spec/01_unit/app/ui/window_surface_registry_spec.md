# Window Surface Registry Specification

> <details>

<!-- sdn-diagram:id=window_surface_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_surface_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_surface_registry_spec -> std
window_surface_registry_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_surface_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Surface Registry Specification

## Scenarios

### UiWindowSurfaceRegistry

#### defines canonical surface kind constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(UI_SURFACE_KIND_LEGACY).to_equal("Legacy")
expect(UI_SURFACE_KIND_SIMPLE_WEB).to_equal("SimpleWeb")
expect(UI_SURFACE_KIND_ELECTRON).to_equal("Electron")
expect(UI_SURFACE_KIND_TAURI).to_equal("Tauri")
expect(UI_SURFACE_KIND_HEADLESS).to_equal("Headless")
```

</details>

#### classifies surface kind capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_surface_kind_is_native_host(UI_SURFACE_KIND_ELECTRON)).to_equal(true)
expect(ui_surface_kind_is_native_host(UI_SURFACE_KIND_TAURI)).to_equal(true)
expect(ui_surface_kind_is_native_host(UI_SURFACE_KIND_SIMPLE_WEB)).to_equal(false)
expect(ui_surface_kind_supports_embedded_surface(UI_SURFACE_KIND_SIMPLE_WEB)).to_equal(true)
expect(ui_surface_kind_supports_embedded_surface(UI_SURFACE_KIND_TAURI)).to_equal(false)
expect(ui_surface_kind_supports_embedded_surface(UI_SURFACE_KIND_ELECTRON)).to_equal(false)
expect(ui_surface_kind_supports_headless_session(UI_SURFACE_KIND_HEADLESS)).to_equal(true)
```

</details>

#### binds windows to surfaces and supports one-to-one replacement

1. var registry = UiWindowSurfaceRegistry new
2. registry bind
   - Expected: registry.len() equals `1`
   - Expected: registry.window_id_for_surface("main") equals `1`
   - Expected: registry.surface_kind_for_surface("main") equals `UI_SURFACE_KIND_LEGACY`
3. registry bind
   - Expected: registry.len() equals `1`
   - Expected: registry.window_id_for_surface("main") equals `2`
4. registry bind
   - Expected: registry.len() equals `1`
   - Expected: registry.window_id_for_surface("popup") equals `2`
   - Expected: registry.window_id_for_surface("main") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = UiWindowSurfaceRegistry.new()
registry.bind("1", "main", 101, "app.main", "Main")
expect(registry.len()).to_equal(1)
expect(registry.window_id_for_surface("main")).to_equal("1")
expect(registry.surface_kind_for_surface("main")).to_equal(UI_SURFACE_KIND_LEGACY)

registry.bind("2", "main", 202, "app.main", "Main 2")
expect(registry.len()).to_equal(1)
expect(registry.window_id_for_surface("main")).to_equal("2")

registry.bind("2", "popup", 202, "app.popup", "Popup")
expect(registry.len()).to_equal(1)
expect(registry.window_id_for_surface("popup")).to_equal("2")
expect(registry.window_id_for_surface("main")).to_equal("")
```

</details>

#### clears bindings by surface and by window

1. var registry = UiWindowSurfaceRegistry new
2. registry bind
3. registry bind
4. registry clear surface
   - Expected: registry.window_id_for_surface("main") equals ``
   - Expected: registry.window_id_for_surface("popup") equals `4`
5. registry clear window
   - Expected: registry.window_id_for_surface("popup") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = UiWindowSurfaceRegistry.new()
registry.bind("3", "main", 303, "app.main", "Main")
registry.bind("4", "popup", 404, "app.popup", "Popup")
registry.clear_surface("main")
expect(registry.window_id_for_surface("main")).to_equal("")
expect(registry.window_id_for_surface("popup")).to_equal("4")
registry.clear_window("4")
expect(registry.window_id_for_surface("popup")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/window_surface_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UiWindowSurfaceRegistry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
