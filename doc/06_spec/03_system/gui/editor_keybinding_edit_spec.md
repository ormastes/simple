# Editor Keybinding Edit Specification

> Tests covering keybinding_config_add, keybinding_config_remove, keybinding_config_update, keybinding_config_find_by_key, keybinding_config_find_by_command, keybinding_config_save, keybinding_config_to_sdn, keybinding settings schema.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Keybinding Edit Specification

## Scenarios

### keybinding_config_add

#### defines keybinding_config_add function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines keybinding_config_add function
   - Expected: src contains `fn keybinding_config_add(config: KeybindingConfig, binding: KeyBinding) -> Ke... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_add function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_add(config: KeybindingConfig, binding: KeyBinding) -> KeybindingConfig")).to_equal(true)
```

</details>

#### appends new binding to config bindings

- appends new binding to config bindings
   - Expected: src contains `bindings.push(binding)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("appends new binding to config bindings")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("bindings.push(binding)")).to_equal(true)
```

</details>

### keybinding_config_remove

#### defines keybinding_config_remove function

- defines keybinding_config_remove function
   - Expected: src contains `fn keybinding_config_remove(config: KeybindingConfig, index: i64) -> Keybindi... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_remove function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_remove(config: KeybindingConfig, index: i64) -> KeybindingConfig")).to_equal(true)
```

</details>

#### skips the element at the given index

- skips the element at the given index
   - Expected: src contains `if i != index`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips the element at the given index")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("if i != index")).to_equal(true)
```

</details>

### keybinding_config_update

#### defines keybinding_config_update function

- defines keybinding_config_update function
   - Expected: src contains `fn keybinding_config_update(config: KeybindingConfig, index: i64, binding: Ke... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_update function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_update(config: KeybindingConfig, index: i64, binding: KeyBinding) -> KeybindingConfig")).to_equal(true)
```

</details>

#### replaces binding at the given index

- replaces binding at the given index
   - Expected: src contains `if i == index`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces binding at the given index")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("if i == index")).to_equal(true)
```

</details>

### keybinding_config_find_by_key

#### defines keybinding_config_find_by_key function

- defines keybinding_config_find_by_key function
   - Expected: src contains `fn keybinding_config_find_by_key(config: KeybindingConfig, key: text) -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_find_by_key function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_find_by_key(config: KeybindingConfig, key: text) -> i64")).to_equal(true)
```

</details>

#### returns -1 when key is not found

- returns -1 when key is not found
   - Expected: src contains `fn keybinding_config_find_by_key`
   - Expected: src contains `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns -1 when key is not found")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_find_by_key")).to_equal(true)
expect(src.contains("-1")).to_equal(true)
```

</details>

### keybinding_config_find_by_command

#### defines keybinding_config_find_by_command function

- defines keybinding_config_find_by_command function
   - Expected: src contains `fn keybinding_config_find_by_command(config: KeybindingConfig, command: text)... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_find_by_command function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_find_by_command(config: KeybindingConfig, command: text) -> i64")).to_equal(true)
```

</details>

#### searches bindings by command field

- searches bindings by command field
   - Expected: src contains `b.command == command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("searches bindings by command field")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("b.command == command")).to_equal(true)
```

</details>

### keybinding_config_save

#### defines keybinding_config_save function

- defines keybinding_config_save function
   - Expected: src contains `fn keybinding_config_save(config: KeybindingConfig, path: text) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_save function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_save(config: KeybindingConfig, path: text) -> bool")).to_equal(true)
```

</details>

#### calls rt_file_write_text to persist config

- calls rt_file_write_text to persist config
   - Expected: src contains `rt_file_write_text(path, content)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls rt_file_write_text to persist config")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("rt_file_write_text(path, content)")).to_equal(true)
```

</details>

### keybinding_config_to_sdn

#### defines keybinding_config_to_sdn function

- defines keybinding_config_to_sdn function
   - Expected: src contains `fn keybinding_config_to_sdn(config: KeybindingConfig) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_config_to_sdn function")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("fn keybinding_config_to_sdn(config: KeybindingConfig) -> text")).to_equal(true)
```

</details>

#### serializes key field in SDN format

- serializes key field in SDN format
   - Expected: src contains `"key: "`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes key field in SDN format")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"key: \"")).to_equal(true)
```

</details>

#### serializes command field in SDN format

- serializes command field in SDN format
   - Expected: src contains `"command: "`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes command field in SDN format")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"command: \"")).to_equal(true)
```

</details>

#### serializes mode field in SDN format

- serializes mode field in SDN format
   - Expected: src contains `"mode: "`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serializes mode field in SDN format")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("\"mode: \"")).to_equal(true)
```

</details>

### keybinding settings schema

#### keybinding_settings_schema returns non-empty list

- keybinding_settings_schema returns non-empty list
   - Expected: src contains `fn keybinding_settings_schema() -> [SettingDescriptor]`
   - Expected: src contains `category: "Keybindings"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keybinding_settings_schema returns non-empty list")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn keybinding_settings_schema() -> [SettingDescriptor]")).to_equal(true)
expect(src.contains("category: \"Keybindings\"")).to_equal(true)
```

</details>

#### uses Keybindings category for entries

- uses Keybindings category for entries
   - Expected: src contains `"Keybindings"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses Keybindings category for entries")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("\"Keybindings\"")).to_equal(true)
```

</details>

#### uses text setting_type for keybinding entries

- uses text setting_type for keybinding entries
   - Expected: src contains `setting_type: "text"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses text setting_type for keybinding entries")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering keybinding_config_add, keybinding_config_remove, keybinding_config_update, keybinding_config_find_by_key, keybinding_config_find_by_command, keybinding_config_save, keybinding_config_to_sdn, keybinding settings schema.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6be7a80205ef0b710b3aa916e0c9761e87a7789893d44c01db3347c7dc6f4378`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6be7a80205ef0b710b3aa916e0c9761e87a7789893d44c01db3347c7dc6f4378`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6be7a80205ef0b710b3aa916e0c9761e87a7789893d44c01db3347c7dc6f4378`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_keybinding_edit_spec.spl
mirror: doc/06_spec/03_system/gui/editor_keybinding_edit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_keybinding_edit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_keybinding_edit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_keybinding_edit_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines keybinding_config_add function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_keybinding_edit_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends new binding to config bindings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_keybinding_edit_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines keybinding_config_remove function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
