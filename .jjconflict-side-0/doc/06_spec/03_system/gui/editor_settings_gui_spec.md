# Editor Settings Gui Specification

> <details>

<!-- sdn-diagram:id=editor_settings_gui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_settings_gui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_settings_gui_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_settings_gui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings Gui Specification

## Scenarios

### gui_render_settings_html — html output

#### function exists in gui_backend.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("fn gui_render_settings_html(view: SettingsViewState, config: EditorConfig) -> text")).to_equal(true)
```

</details>

#### wraps output in settings-panel div

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("settings-panel")).to_equal(true)
```

</details>

#### includes search bar with settings-search class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("settings-search")).to_equal(true)
```

</details>

#### renders checkbox for bool settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("type=\\\"checkbox\\\"")).to_equal(true)
```

</details>

#### renders number input for i64 settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("type=\\\"number\\\"")).to_equal(true)
```

</details>

#### renders select element for enum settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/70.backend/gui_backend.spl")
expect(src.contains("<select")).to_equal(true)
```

</details>

### gui_shell — settings integration

#### calls gui_render_settings_html when settings_view is active

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_render.spl")
expect(src.contains("gui_render_settings_html")).to_equal(true)
```

</details>

#### handles settings-change event

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("settings-change")).to_equal(true)
```

</details>

#### parses key and value from settings-change event data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/gui_shell_core.spl")
expect(src.contains("editor_config_set_by_key")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_settings_gui_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gui_render_settings_html — html output
- gui_shell — settings integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
