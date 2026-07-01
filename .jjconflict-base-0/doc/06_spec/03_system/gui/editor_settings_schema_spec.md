# Editor Settings Schema Specification

> <details>

<!-- sdn-diagram:id=editor_settings_schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_settings_schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_settings_schema_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_settings_schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings Schema Specification

## Scenarios

### SettingDescriptor struct

#### defines SettingDescriptor with all required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("struct SettingDescriptor:")).to_equal(true)
expect(src.contains("key: text")).to_equal(true)
expect(src.contains("label: text")).to_equal(true)
expect(src.contains("description: text")).to_equal(true)
expect(src.contains("category: text")).to_equal(true)
expect(src.contains("setting_type: text")).to_equal(true)
expect(src.contains("default_value: text")).to_equal(true)
expect(src.contains("enum_options: [text]")).to_equal(true)
expect(src.contains("platform: text")).to_equal(true)
```

</details>

### editor_settings_schema function

#### defines editor_settings_schema returning descriptor list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn editor_settings_schema() -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### includes theme enum descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"theme\"")).to_equal(true)
expect(src.contains("setting_type: \"enum\"")).to_equal(true)
expect(src.contains("enum_options: [\"dark\", \"light\", \"solarized\"]")).to_equal(true)
```

</details>

#### includes font_size i64 descriptor in Appearance category

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"font_size\"")).to_equal(true)
expect(src.contains("setting_type: \"i64\"")).to_equal(true)
```

</details>

#### includes tab_size in Editor category

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"tab_size\"")).to_equal(true)
expect(src.contains("category: \"Editor\"")).to_equal(true)
```

</details>

#### includes insert_spaces bool in Editor category

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"insert_spaces\"")).to_equal(true)
expect(src.contains("setting_type: \"bool\"")).to_equal(true)
```

</details>

#### includes minimap with desktop platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"minimap\"")).to_equal(true)
expect(src.contains("platform: \"desktop\"")).to_equal(true)
```

</details>

#### includes auto_save and auto_save_delay_ms in Files category

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"auto_save\"")).to_equal(true)
expect(src.contains("key: \"auto_save_delay_ms\"")).to_equal(true)
expect(src.contains("category: \"Files\"")).to_equal(true)
```

</details>

#### includes configurable LSP hover delay in Editor category

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"hover_delay_ms\"")).to_equal(true)
expect(src.contains("label: \"Hover Delay\"")).to_equal(true)
expect(src.contains("key: \"inlay_hint_refresh_delay_ms\"")).to_equal(true)
expect(src.contains("label: \"Inlay Hint Refresh Delay\"")).to_equal(true)
expect(src.contains("default_value: \"300\"")).to_equal(true)
```

</details>

### schema utility functions

#### defines keybinding_settings_schema returning empty placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn keybinding_settings_schema() -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### defines full_settings_schema combining both schemas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn full_settings_schema() -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### defines settings_categories returning category list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_categories() -> [text]")).to_equal(true)
expect(src.contains("\"Editor\"")).to_equal(true)
expect(src.contains("\"Appearance\"")).to_equal(true)
expect(src.contains("\"Keybindings\"")).to_equal(true)
```

</details>

#### defines settings_filter_by_category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_filter_by_category(schema: [SettingDescriptor], category: text) -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### defines settings_filter_by_platform with all-platform fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_filter_by_platform(schema: [SettingDescriptor], platform: text) -> [SettingDescriptor]")).to_equal(true)
expect(src.contains("d.platform == \"all\"")).to_equal(true)
```

</details>

#### defines settings_search

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_search(schema: [SettingDescriptor], query: text) -> [SettingDescriptor]")).to_equal(true)
```

</details>

### editor_config get set save functions

#### defines editor_config_get_by_key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_get_by_key(config: EditorConfig, key: text) -> text")).to_equal(true)
```

</details>

#### defines editor_config_set_by_key returning EditorConfig

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_set_by_key(config: EditorConfig, key: text, value: text) -> EditorConfig")).to_equal(true)
```

</details>

#### defines editor_config_save with path parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_save(config: EditorConfig, path: text) -> bool")).to_equal(true)
expect(src.contains("rt_file_write_text(path, content)")).to_equal(true)
```

</details>

#### declares rt_file_write_text extern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("extern fn rt_file_write_text(path: text, content: text) -> bool")).to_equal(true)
```

</details>

#### applies font_size in _ec_apply_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"font_size\"")).to_equal(true)
```

</details>

#### applies insert_spaces in _ec_apply_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"insert_spaces\"")).to_equal(true)
```

</details>

#### applies word_wrap in _ec_apply_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"word_wrap\"")).to_equal(true)
```

</details>

#### applies minimap in _ec_apply_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"minimap\"")).to_equal(true)
```

</details>

#### applies auto_save_delay_ms in _ec_apply_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"auto_save_delay_ms\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_settings_schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SettingDescriptor struct
- editor_settings_schema function
- schema utility functions
- editor_config get set save functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
