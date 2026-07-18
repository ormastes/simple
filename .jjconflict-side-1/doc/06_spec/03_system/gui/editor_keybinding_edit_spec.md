# Editor Keybinding Edit Specification

> <details>

<!-- sdn-diagram:id=editor_keybinding_edit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_keybinding_edit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_keybinding_edit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_keybinding_edit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Keybinding Edit Specification

## Scenarios

### keybinding_config_add

#### defines keybinding_config_add function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_add(config: KeybindingConfig, binding: KeyBinding) -> KeybindingConfig")).to_equal(true)
```

</details>

#### appends new binding to config bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("bindings.push(binding)")).to_equal(true)
```

</details>

### keybinding_config_remove

#### defines keybinding_config_remove function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_remove(config: KeybindingConfig, index: i64) -> KeybindingConfig")).to_equal(true)
```

</details>

#### skips the element at the given index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("if i != index")).to_equal(true)
```

</details>

### keybinding_config_update

#### defines keybinding_config_update function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_update(config: KeybindingConfig, index: i64, binding: KeyBinding) -> KeybindingConfig")).to_equal(true)
```

</details>

#### replaces binding at the given index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("if i == index")).to_equal(true)
```

</details>

### keybinding_config_find_by_key

#### defines keybinding_config_find_by_key function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_find_by_key(config: KeybindingConfig, key: text) -> i64")).to_equal(true)
```

</details>

#### returns -1 when key is not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_find_by_key")).to_equal(true)
expect(src.contains("-1")).to_equal(true)
```

</details>

### keybinding_config_find_by_command

#### defines keybinding_config_find_by_command function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_find_by_command(config: KeybindingConfig, command: text) -> i64")).to_equal(true)
```

</details>

#### searches bindings by command field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("b.command == command")).to_equal(true)
```

</details>

### keybinding_config_save

#### defines keybinding_config_save function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_save(config: KeybindingConfig, path: text) -> bool")).to_equal(true)
```

</details>

#### calls rt_file_write_text to persist config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("rt_file_write_text(path, content)")).to_equal(true)
```

</details>

### keybinding_config_to_sdn

#### defines keybinding_config_to_sdn function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_to_sdn(config: KeybindingConfig) -> text")).to_equal(true)
```

</details>

#### serializes key field in SDN format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"key: \"")).to_equal(true)
```

</details>

#### serializes command field in SDN format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"command: \"")).to_equal(true)
```

</details>

#### serializes mode field in SDN format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"mode: \"")).to_equal(true)
```

</details>

### keybinding settings schema

#### keybinding_settings_schema returns non-empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn keybinding_settings_schema() -> [SettingDescriptor]")).to_equal(true)
expect(src.contains("category: \"Keybindings\"")).to_equal(true)
```

</details>

#### uses Keybindings category for entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("\"Keybindings\"")).to_equal(true)
```

</details>

#### uses text setting_type for keybinding entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("setting_type: \"text\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_keybinding_edit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- keybinding_config_add
- keybinding_config_remove
- keybinding_config_update
- keybinding_config_find_by_key
- keybinding_config_find_by_command
- keybinding_config_save
- keybinding_config_to_sdn
- keybinding settings schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
