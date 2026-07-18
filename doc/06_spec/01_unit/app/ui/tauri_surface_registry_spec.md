# Tauri Surface Registry Specification

> <details>

<!-- sdn-diagram:id=tauri_surface_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_surface_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_surface_registry_spec -> std
tauri_surface_registry_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_surface_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri Surface Registry Specification

## Scenarios

### app.ui.tauri.surface_registry

#### exposes a Tauri registry helper in the shared-WM Tauri entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source("src/app/ui.tauri/async_app.spl")
expect(source).to_contain("fn register_tauri_window")
expect(source).to_contain("UI_SURFACE_KIND_TAURI")
expect(source).to_contain("reg.bind_with_kind(window_id, surface_id, process_id, app_id, title, UI_SURFACE_KIND_TAURI)")
```

</details>

#### binds a Tauri window with the Tauri surface kind

1.  register tauri window
   - Expected: binding == nil is false
   - Expected: binding.surface_kind equals `UI_SURFACE_KIND_TAURI`
   - Expected: reg.window_id_for_surface("surface-tauri") equals `window-tauri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = new_ui_window_surface_registry()
_register_tauri_window(reg, "surface-tauri", "window-tauri", 77 as u64, "app.tauri", "Tauri")
val binding = reg.for_surface("surface-tauri")
expect(binding == nil).to_equal(false)
expect(binding.surface_kind).to_equal(UI_SURFACE_KIND_TAURI)
expect(reg.window_id_for_surface("surface-tauri")).to_equal("window-tauri")
```

</details>

#### replaces prior bindings through the shared one-to-one registry rule

1.  register tauri window
2.  register tauri window
   - Expected: reg.len() equals `1`
   - Expected: reg.window_id_for_surface("surface-one") equals ``
   - Expected: reg.window_id_for_surface("surface-two") equals `window-tauri`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = new_ui_window_surface_registry()
_register_tauri_window(reg, "surface-one", "window-tauri", 77 as u64, "app.tauri", "One")
_register_tauri_window(reg, "surface-two", "window-tauri", 77 as u64, "app.tauri", "Two")
expect(reg.len()).to_equal(1)
expect(reg.window_id_for_surface("surface-one")).to_equal("")
expect(reg.window_id_for_surface("surface-two")).to_equal("window-tauri")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/tauri_surface_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app.ui.tauri.surface_registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
