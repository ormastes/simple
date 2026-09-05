# Editor Keybinding Specification

> <details>

<!-- sdn-diagram:id=editor_keybinding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_keybinding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_keybinding_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_keybinding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Keybinding Specification

## Scenarios

### keybinding structs

#### defines KeyBinding with key, command, mode, args

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("struct KeyBinding:")).to_equal(true)
expect(src.contains("key: text")).to_equal(true)
expect(src.contains("command: text")).to_equal(true)
expect(src.contains("mode: text")).to_equal(true)
expect(src.contains("args: text")).to_equal(true)
```

</details>

#### defines KeybindingConfig with bindings list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("struct KeybindingConfig:")).to_equal(true)
expect(src.contains("bindings: [KeyBinding]")).to_equal(true)
```

</details>

### keybinding defaults

#### defines default_keybindings function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn default_keybindings() -> KeybindingConfig")).to_equal(true)
```

</details>

#### maps h to move-left in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"h\", command: \"move-left\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps j to move-down in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"j\", command: \"move-down\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps k to move-up in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"k\", command: \"move-up\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps l to move-right in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"l\", command: \"move-right\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps i to enter-insert in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"i\", command: \"enter-insert\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps a to append in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"a\", command: \"append\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps o to open-line in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"o\", command: \"open-line\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps colon to enter-command in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \":\", command: \"enter-command\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps q to quit in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"q\", command: \"quit\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps 0 to move-line-start in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"0\", command: \"move-line-start\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps dollar to move-line-end in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"$\", command: \"move-line-end\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps G to move-file-bottom in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"G\", command: \"move-file-bottom\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps g to move-file-top in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"g\", command: \"move-file-top\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps x to delete in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"x\", command: \"delete\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps u to undo in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"u\", command: \"undo\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps Ctrl+R to redo in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x12\", command: \"redo\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps VSCode expand and shrink selection chords in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"Shift+Alt+Right\", command: \"selection-expand\", mode: \"normal\"")).to_equal(true)
expect(src.contains("key: \"Shift+Alt+Left\", command: \"selection-shrink\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps normal-mode K to hover

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"K\", command: \"hover\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps F5 to process-backed debugging in normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"F5\", command: \"debug-process-start\", mode: \"normal\", args: \"simple\"")).to_equal(true)
```

</details>

#### maps Escape to exit-insert in insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x1b\", command: \"exit-insert\", mode: \"insert\"")).to_equal(true)
```

</details>

#### maps Backspace to backspace in insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x7f\", command: \"backspace\", mode: \"insert\"")).to_equal(true)
```

</details>

#### maps Enter to newline in insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\r\", command: \"newline\", mode: \"insert\"")).to_equal(true)
```

</details>

#### maps Escape to cancel in command mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x1b\", command: \"cancel\", mode: \"command\"")).to_equal(true)
```

</details>

#### maps Enter to execute in command mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\r\", command: \"execute\", mode: \"command\"")).to_equal(true)
```

</details>

### keybinding config loading

#### defines keybinding_config_load function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_load(path: text) -> KeybindingConfig")).to_equal(true)
```

</details>

#### returns empty config for missing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("KeybindingConfig(bindings: [])")).to_equal(true)
```

</details>

#### parses SDN line format with key, command, mode labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn _kb_parse_line(line: text) -> KeyBinding")).to_equal(true)
expect(src.contains("key: ")).to_equal(true)
expect(src.contains("command: ")).to_equal(true)
expect(src.contains("mode: ")).to_equal(true)
```

</details>

#### skips comments and empty lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("line.starts_with(\"#\")")).to_equal(true)
```

</details>

### keybinding merge

#### defines keybinding_config_merge function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_merge(defaults: KeybindingConfig, user: KeybindingConfig) -> KeybindingConfig")).to_equal(true)
```

</details>

#### uses key+mode pair for override matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn _kb_find_binding(bindings: [KeyBinding], key: text, mode: text) -> i64")).to_equal(true)
```

</details>

#### appends user-only bindings not in defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("exists < 0")).to_equal(true)
expect(src.contains("result.push(ub)")).to_equal(true)
```

</details>

### keybinding resolve

#### defines resolve_key function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn resolve_key(config: KeybindingConfig, key: text, mode: text) -> text")).to_equal(true)
```

</details>

#### returns empty string when key not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"\"")).to_equal(true)
```

</details>

### keybinding count

#### defines keybinding_count function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_count(config: KeybindingConfig) -> i64")).to_equal(true)
```

</details>

#### returns length of bindings list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("config.bindings.len()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_keybinding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- keybinding structs
- keybinding defaults
- keybinding config loading
- keybinding merge
- keybinding resolve
- keybinding count

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
