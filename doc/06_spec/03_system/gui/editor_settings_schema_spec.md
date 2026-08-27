# Editor Settings Schema Specification

> Tests covering SettingDescriptor struct, editor_settings_schema function, schema utility functions, editor_config get set save functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings Schema Specification

## Scenarios

### SettingDescriptor struct

#### defines SettingDescriptor with all required fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines SettingDescriptor with all required fields
   - Expected: src contains `struct SettingDescriptor:`
   - Expected: src contains `key: text`
   - Expected: src contains `label: text`
   - Expected: src contains `description: text`
   - Expected: src contains `category: text`
   - Expected: src contains `setting_type: text`
   - Expected: src contains `default_value: text`
   - Expected: src contains `enum_options: [text]`
   - Expected: src contains `platform: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SettingDescriptor with all required fields")
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

- defines editor_settings_schema returning descriptor list
   - Expected: src contains `fn editor_settings_schema() -> [SettingDescriptor]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_settings_schema returning descriptor list")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn editor_settings_schema() -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### includes theme enum descriptor

- includes theme enum descriptor
   - Expected: src contains `key: "theme"`
   - Expected: src contains `setting_type: "enum"`
   - Expected: src contains `enum_options: ["dark", "light", "solarized"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes theme enum descriptor")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"theme\"")).to_equal(true)
expect(src.contains("setting_type: \"enum\"")).to_equal(true)
expect(src.contains("enum_options: [\"dark\", \"light\", \"solarized\"]")).to_equal(true)
```

</details>

#### includes font_size i64 descriptor in Appearance category

- includes font_size i64 descriptor in Appearance category
   - Expected: src contains `key: "font_size"`
   - Expected: src contains `setting_type: "i64"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes font_size i64 descriptor in Appearance category")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"font_size\"")).to_equal(true)
expect(src.contains("setting_type: \"i64\"")).to_equal(true)
```

</details>

#### includes tab_size in Editor category

- includes tab_size in Editor category
   - Expected: src contains `key: "tab_size"`
   - Expected: src contains `category: "Editor"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes tab_size in Editor category")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"tab_size\"")).to_equal(true)
expect(src.contains("category: \"Editor\"")).to_equal(true)
```

</details>

#### includes insert_spaces bool in Editor category

- includes insert_spaces bool in Editor category
   - Expected: src contains `key: "insert_spaces"`
   - Expected: src contains `setting_type: "bool"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes insert_spaces bool in Editor category")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"insert_spaces\"")).to_equal(true)
expect(src.contains("setting_type: \"bool\"")).to_equal(true)
```

</details>

#### includes minimap with desktop platform

- includes minimap with desktop platform
   - Expected: src contains `key: "minimap"`
   - Expected: src contains `platform: "desktop"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes minimap with desktop platform")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"minimap\"")).to_equal(true)
expect(src.contains("platform: \"desktop\"")).to_equal(true)
```

</details>

#### includes auto_save and auto_save_delay_ms in Files category

- includes auto_save and auto_save_delay_ms in Files category
   - Expected: src contains `key: "auto_save"`
   - Expected: src contains `key: "auto_save_delay_ms"`
   - Expected: src contains `category: "Files"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes auto_save and auto_save_delay_ms in Files category")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"auto_save\"")).to_equal(true)
expect(src.contains("key: \"auto_save_delay_ms\"")).to_equal(true)
expect(src.contains("category: \"Files\"")).to_equal(true)
```

</details>

#### includes configurable LSP hover delay in Editor category

- includes configurable LSP hover delay in Editor category
   - Expected: src contains `key: "hover_delay_ms"`
   - Expected: src contains `label: "Hover Delay"`
   - Expected: src contains `key: "inlay_hint_refresh_delay_ms"`
   - Expected: src contains `label: "Inlay Hint Refresh Delay"`
   - Expected: src contains `default_value: "300"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes configurable LSP hover delay in Editor category")
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

- defines keybinding_settings_schema returning empty placeholder
   - Expected: src contains `fn keybinding_settings_schema() -> [SettingDescriptor]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines keybinding_settings_schema returning empty placeholder")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn keybinding_settings_schema() -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### defines full_settings_schema combining both schemas

- defines full_settings_schema combining both schemas
   - Expected: src contains `fn full_settings_schema() -> [SettingDescriptor]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines full_settings_schema combining both schemas")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn full_settings_schema() -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### defines settings_categories returning category list

- defines settings_categories returning category list
   - Expected: src contains `fn settings_categories() -> [text]`
   - Expected: src contains `"Editor"`
   - Expected: src contains `"Appearance"`
   - Expected: src contains `"Keybindings"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines settings_categories returning category list")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_categories() -> [text]")).to_equal(true)
expect(src.contains("\"Editor\"")).to_equal(true)
expect(src.contains("\"Appearance\"")).to_equal(true)
expect(src.contains("\"Keybindings\"")).to_equal(true)
```

</details>

#### defines settings_filter_by_category

- defines settings_filter_by_category
   - Expected: src contains `fn settings_filter_by_category(schema: [SettingDescriptor], category: text) -... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines settings_filter_by_category")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_filter_by_category(schema: [SettingDescriptor], category: text) -> [SettingDescriptor]")).to_equal(true)
```

</details>

#### defines settings_filter_by_platform with all-platform fallback

- defines settings_filter_by_platform with all-platform fallback
   - Expected: src contains `fn settings_filter_by_platform(schema: [SettingDescriptor], platform: text) -... (full value in folded executable source)`
   - Expected: src contains `d.platform == "all"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines settings_filter_by_platform with all-platform fallback")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_filter_by_platform(schema: [SettingDescriptor], platform: text) -> [SettingDescriptor]")).to_equal(true)
expect(src.contains("d.platform == \"all\"")).to_equal(true)
```

</details>

#### defines settings_search

- defines settings_search
   - Expected: src contains `fn settings_search(schema: [SettingDescriptor], query: text) -> [SettingDescr... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines settings_search")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("fn settings_search(schema: [SettingDescriptor], query: text) -> [SettingDescriptor]")).to_equal(true)
```

</details>

### editor_config get set save functions

#### defines editor_config_get_by_key

- defines editor_config_get_by_key
   - Expected: src contains `fn editor_config_get_by_key(config: EditorConfig, key: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_config_get_by_key")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_get_by_key(config: EditorConfig, key: text) -> text")).to_equal(true)
```

</details>

#### defines editor_config_set_by_key returning EditorConfig

- defines editor_config_set_by_key returning EditorConfig
   - Expected: src contains `fn editor_config_set_by_key(config: EditorConfig, key: text, value: text) -> ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_config_set_by_key returning EditorConfig")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_set_by_key(config: EditorConfig, key: text, value: text) -> EditorConfig")).to_equal(true)
```

</details>

#### defines editor_config_save with path parameter

- defines editor_config_save with path parameter
   - Expected: src contains `fn editor_config_save(config: EditorConfig, path: text) -> bool`
   - Expected: src contains `rt_file_write_text(path, content)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines editor_config_save with path parameter")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("fn editor_config_save(config: EditorConfig, path: text) -> bool")).to_equal(true)
expect(src.contains("rt_file_write_text(path, content)")).to_equal(true)
```

</details>

#### declares rt_file_write_text extern

- declares rt_file_write_text extern
   - Expected: src contains `extern fn rt_file_write_text(path: text, content: text) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares rt_file_write_text extern")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("extern fn rt_file_write_text(path: text, content: text) -> bool")).to_equal(true)
```

</details>

#### applies font_size in _ec_apply_line

- applies font_size in _ec_apply_line
   - Expected: src contains `key == "font_size"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies font_size in _ec_apply_line")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"font_size\"")).to_equal(true)
```

</details>

#### applies insert_spaces in _ec_apply_line

- applies insert_spaces in _ec_apply_line
   - Expected: src contains `key == "insert_spaces"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies insert_spaces in _ec_apply_line")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"insert_spaces\"")).to_equal(true)
```

</details>

#### applies word_wrap in _ec_apply_line

- applies word_wrap in _ec_apply_line
   - Expected: src contains `key == "word_wrap"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies word_wrap in _ec_apply_line")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"word_wrap\"")).to_equal(true)
```

</details>

#### applies minimap in _ec_apply_line

- applies minimap in _ec_apply_line
   - Expected: src contains `key == "minimap"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies minimap in _ec_apply_line")
val src = read_text("src/lib/editor/00.common/config.spl")
expect(src.contains("key == \"minimap\"")).to_equal(true)
```

</details>

#### applies auto_save_delay_ms in _ec_apply_line

- applies auto_save_delay_ms in _ec_apply_line
   - Expected: src contains `key == "auto_save_delay_ms"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies auto_save_delay_ms in _ec_apply_line")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SettingDescriptor struct, editor_settings_schema function, schema utility functions, editor_config get set save functions.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0ab336c67bcf0f32b8eb1d45e24494c8cb65b602a74f88ebe8702acd14567ab7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ab336c67bcf0f32b8eb1d45e24494c8cb65b602a74f88ebe8702acd14567ab7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ab336c67bcf0f32b8eb1d45e24494c8cb65b602a74f88ebe8702acd14567ab7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_settings_schema_spec.spl
mirror: doc/06_spec/03_system/gui/editor_settings_schema_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_settings_schema_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_settings_schema_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_settings_schema_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SettingDescriptor with all required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_schema_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines editor_settings_schema returning descriptor list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_schema_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes theme enum descriptor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
