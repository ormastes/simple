# Editor Keybinding Specification

> Tests covering keybinding structs, keybinding defaults, keybinding config loading, keybinding merge, keybinding resolve, keybinding count.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Keybinding Specification

## Scenarios

### keybinding structs

#### defines KeyBinding with key, command, mode, args

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines KeyBinding with key, command, mode, args
   - Expected: src contains `struct KeyBinding:`
   - Expected: src contains `key: text`
   - Expected: src contains `command: text`
   - Expected: src contains `mode: text`
   - Expected: src contains `args: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines KeyBinding with key, command, mode, args")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("struct KeyBinding:")).to_equal(true)
expect(src.contains("key: text")).to_equal(true)
expect(src.contains("command: text")).to_equal(true)
expect(src.contains("mode: text")).to_equal(true)
expect(src.contains("args: text")).to_equal(true)
```

</details>

#### defines KeybindingConfig with bindings list

- defines KeybindingConfig with bindings list
   - Expected: src contains `struct KeybindingConfig:`
   - Expected: src contains `bindings: [KeyBinding]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines KeybindingConfig with bindings list")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("struct KeybindingConfig:")).to_equal(true)
expect(src.contains("bindings: [KeyBinding]")).to_equal(true)
```

</details>

### keybinding defaults

#### defines default_keybindings function

- defines default_keybindings function
   - Expected: src contains `fn default_keybindings() -> KeybindingConfig`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines default_keybindings function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn default_keybindings() -> KeybindingConfig")).to_equal(true)
```

</details>

#### maps h to move-left in normal mode

- maps h to move-left in normal mode
   - Expected: src contains `key: "h", command: "move-left", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps h to move-left in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"h\", command: \"move-left\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps j to move-down in normal mode

- maps j to move-down in normal mode
   - Expected: src contains `key: "j", command: "move-down", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps j to move-down in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"j\", command: \"move-down\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps k to move-up in normal mode

- maps k to move-up in normal mode
   - Expected: src contains `key: "k", command: "move-up", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps k to move-up in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"k\", command: \"move-up\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps l to move-right in normal mode

- maps l to move-right in normal mode
   - Expected: src contains `key: "l", command: "move-right", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps l to move-right in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"l\", command: \"move-right\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps i to enter-insert in normal mode

- maps i to enter-insert in normal mode
   - Expected: src contains `key: "i", command: "enter-insert", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps i to enter-insert in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"i\", command: \"enter-insert\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps a to append in normal mode

- maps a to append in normal mode
   - Expected: src contains `key: "a", command: "append", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps a to append in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"a\", command: \"append\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps o to open-line in normal mode

- maps o to open-line in normal mode
   - Expected: src contains `key: "o", command: "open-line", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps o to open-line in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"o\", command: \"open-line\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps colon to enter-command in normal mode

- maps colon to enter-command in normal mode
   - Expected: src contains `key: ":", command: "enter-command", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps colon to enter-command in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \":\", command: \"enter-command\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps q to quit in normal mode

- maps q to quit in normal mode
   - Expected: src contains `key: "q", command: "quit", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps q to quit in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"q\", command: \"quit\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps 0 to move-line-start in normal mode

- maps 0 to move-line-start in normal mode
   - Expected: src contains `key: "0", command: "move-line-start", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps 0 to move-line-start in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"0\", command: \"move-line-start\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps dollar to move-line-end in normal mode

- maps dollar to move-line-end in normal mode
   - Expected: src contains `key: "$", command: "move-line-end", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps dollar to move-line-end in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"$\", command: \"move-line-end\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps G to move-file-bottom in normal mode

- maps G to move-file-bottom in normal mode
   - Expected: src contains `key: "G", command: "move-file-bottom", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps G to move-file-bottom in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"G\", command: \"move-file-bottom\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps g to move-file-top in normal mode

- maps g to move-file-top in normal mode
   - Expected: src contains `key: "g", command: "move-file-top", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps g to move-file-top in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"g\", command: \"move-file-top\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps x to delete in normal mode

- maps x to delete in normal mode
   - Expected: src contains `key: "x", command: "delete", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps x to delete in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"x\", command: \"delete\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps u to undo in normal mode

- maps u to undo in normal mode
   - Expected: src contains `key: "u", command: "undo", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps u to undo in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"u\", command: \"undo\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps Ctrl+R to redo in normal mode

- maps Ctrl+R to redo in normal mode
   - Expected: src contains `key: "\\x12", command: "redo", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps Ctrl+R to redo in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x12\", command: \"redo\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps VSCode expand and shrink selection chords in normal mode

- maps VSCode expand and shrink selection chords in normal mode
   - Expected: src contains `key: "Shift+Alt+Right", command: "selection-expand", mode: "normal"`
   - Expected: src contains `key: "Shift+Alt+Left", command: "selection-shrink", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps VSCode expand and shrink selection chords in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"Shift+Alt+Right\", command: \"selection-expand\", mode: \"normal\"")).to_equal(true)
expect(src.contains("key: \"Shift+Alt+Left\", command: \"selection-shrink\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps normal-mode K to hover

- maps normal-mode K to hover
   - Expected: src contains `key: "K", command: "hover", mode: "normal"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps normal-mode K to hover")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"K\", command: \"hover\", mode: \"normal\"")).to_equal(true)
```

</details>

#### maps F5 to process-backed debugging in normal mode

- maps F5 to process-backed debugging in normal mode
   - Expected: src contains `key: "F5", command: "debug-process-start", mode: "normal", args: "simple"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps F5 to process-backed debugging in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"F5\", command: \"debug-process-start\", mode: \"normal\", args: \"simple\"")).to_equal(true)
```

</details>

#### maps Escape to exit-insert in insert mode

- maps Escape to exit-insert in insert mode
   - Expected: src contains `key: "\\x1b", command: "exit-insert", mode: "insert"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps Escape to exit-insert in insert mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x1b\", command: \"exit-insert\", mode: \"insert\"")).to_equal(true)
```

</details>

#### maps Backspace to backspace in insert mode

- maps Backspace to backspace in insert mode
   - Expected: src contains `key: "\\x7f", command: "backspace", mode: "insert"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps Backspace to backspace in insert mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x7f\", command: \"backspace\", mode: \"insert\"")).to_equal(true)
```

</details>

#### maps Enter to newline in insert mode

- maps Enter to newline in insert mode
   - Expected: src contains `key: "\\r", command: "newline", mode: "insert"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps Enter to newline in insert mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\r\", command: \"newline\", mode: \"insert\"")).to_equal(true)
```

</details>

#### maps Escape to cancel in command mode

- maps Escape to cancel in command mode
   - Expected: src contains `key: "\\x1b", command: "cancel", mode: "command"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps Escape to cancel in command mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\x1b\", command: \"cancel\", mode: \"command\"")).to_equal(true)
```

</details>

#### maps Enter to execute in command mode

- maps Enter to execute in command mode
   - Expected: src contains `key: "\\r", command: "execute", mode: "command"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps Enter to execute in command mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("key: \"\\r\", command: \"execute\", mode: \"command\"")).to_equal(true)
```

</details>

### keybinding config loading

#### defines keybinding_config_load function

- defines keybinding_config_load function
   - Expected: src contains `fn keybinding_config_load(path: text) -> KeybindingConfig`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_load function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_load(path: text) -> KeybindingConfig")).to_equal(true)
```

</details>

#### returns empty config for missing file

- returns empty config for missing file
   - Expected: src contains `KeybindingConfig(bindings: [])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty config for missing file")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("KeybindingConfig(bindings: [])")).to_equal(true)
```

</details>

#### parses SDN line format with key, command, mode labels

- parses SDN line format with key, command, mode labels
   - Expected: src contains `fn _kb_parse_line(line: text) -> KeyBinding`
   - Expected: src contains `key: `
   - Expected: src contains `command: `
   - Expected: src contains `mode: `


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses SDN line format with key, command, mode labels")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn _kb_parse_line(line: text) -> KeyBinding")).to_equal(true)
expect(src.contains("key: ")).to_equal(true)
expect(src.contains("command: ")).to_equal(true)
expect(src.contains("mode: ")).to_equal(true)
```

</details>

#### skips comments and empty lines

- skips comments and empty lines
   - Expected: src contains `line.starts_with("#")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips comments and empty lines")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("line.starts_with(\"#\")")).to_equal(true)
```

</details>

### keybinding merge

#### defines keybinding_config_merge function

- defines keybinding_config_merge function
   - Expected: src contains `fn keybinding_config_merge(defaults: KeybindingConfig, user: KeybindingConfig... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_merge function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_merge(defaults: KeybindingConfig, user: KeybindingConfig) -> KeybindingConfig")).to_equal(true)
```

</details>

#### uses key+mode pair for override matching

- uses key+mode pair for override matching
   - Expected: src contains `fn _kb_find_binding(bindings: [KeyBinding], key: text, mode: text) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses key+mode pair for override matching")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn _kb_find_binding(bindings: [KeyBinding], key: text, mode: text) -> i64")).to_equal(true)
```

</details>

#### appends user-only bindings not in defaults

- appends user-only bindings not in defaults
   - Expected: src contains `exists < 0`
   - Expected: src contains `result.push(ub)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("appends user-only bindings not in defaults")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("exists < 0")).to_equal(true)
expect(src.contains("result.push(ub)")).to_equal(true)
```

</details>

### keybinding resolve

#### defines resolve_key function

- defines resolve_key function
   - Expected: src contains `fn resolve_key(config: KeybindingConfig, key: text, mode: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines resolve_key function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn resolve_key(config: KeybindingConfig, key: text, mode: text) -> text")).to_equal(true)
```

</details>

#### returns empty string when key not found

- returns empty string when key not found
   - Expected: src contains `""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string when key not found")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"\"")).to_equal(true)
```

</details>

### keybinding count

#### defines keybinding_count function

- defines keybinding_count function
   - Expected: src contains `fn keybinding_count(config: KeybindingConfig) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_count function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_count(config: KeybindingConfig) -> i64")).to_equal(true)
```

</details>

#### returns length of bindings list

- returns length of bindings list
   - Expected: src contains `config.bindings.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns length of bindings list")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering keybinding structs, keybinding defaults, keybinding config loading, keybinding merge, keybinding resolve, keybinding count.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e2f10ac824cca6c56ce005eb3107a9d358df0f1ff3551e4f9b8e79dbbcc6aec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e2f10ac824cca6c56ce005eb3107a9d358df0f1ff3551e4f9b8e79dbbcc6aec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e2f10ac824cca6c56ce005eb3107a9d358df0f1ff3551e4f9b8e79dbbcc6aec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_keybinding_spec.spl
mirror: doc/06_spec/03_system/gui/editor_keybinding_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_keybinding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_keybinding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_keybinding_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines KeyBinding with key, command, mode, args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_keybinding_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines KeybindingConfig with bindings list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_keybinding_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines default_keybindings function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
