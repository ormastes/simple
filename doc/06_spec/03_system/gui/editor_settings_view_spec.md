# Editor Settings View Specification

> Tests covering SettingsViewState class, EditorController settings integration, TUI settings rendering, commands.spl settings command.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings View Specification

## Scenarios

### SettingsViewState class

#### defines SettingsViewState with all required fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines SettingsViewState with all required fields
   - Expected: src contains `class SettingsViewState:`
   - Expected: src contains `schema:`
   - Expected: src contains `filtered:`
   - Expected: src contains `selected_index:`
   - Expected: src contains `category_index:`
   - Expected: src contains `categories:`
   - Expected: src contains `search_query:`
   - Expected: src contains `editing:`
   - Expected: src contains `edit_value:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SettingsViewState with all required fields")
val src = read_text("src/lib/editor/view/settings_view.spl")
expect(src.contains("class SettingsViewState:")).to_equal(true)
expect(src.contains("schema:")).to_equal(true)
expect(src.contains("filtered:")).to_equal(true)
expect(src.contains("selected_index:")).to_equal(true)
expect(src.contains("category_index:")).to_equal(true)
expect(src.contains("categories:")).to_equal(true)
expect(src.contains("search_query:")).to_equal(true)
expect(src.contains("editing:")).to_equal(true)
expect(src.contains("edit_value:")).to_equal(true)
```

</details>

#### defines required methods on SettingsViewState

- defines required methods on SettingsViewState
   - Expected: src contains `static fn new(`
   - Expected: src contains `me select_next()`
   - Expected: src contains `me select_prev()`
   - Expected: src contains `me next_category()`
   - Expected: src contains `me prev_category()`
   - Expected: src contains `me apply_filter()`
   - Expected: src contains `me start_edit(`
   - Expected: src contains `me cancel_edit()`
   - Expected: src contains `fn current_setting()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines required methods on SettingsViewState")
val src = read_text("src/lib/editor/view/settings_view.spl")
expect(src.contains("static fn new(")).to_equal(true)
expect(src.contains("me select_next()")).to_equal(true)
expect(src.contains("me select_prev()")).to_equal(true)
expect(src.contains("me next_category()")).to_equal(true)
expect(src.contains("me prev_category()")).to_equal(true)
expect(src.contains("me apply_filter()")).to_equal(true)
expect(src.contains("me start_edit(")).to_equal(true)
expect(src.contains("me cancel_edit()")).to_equal(true)
expect(src.contains("fn current_setting()")).to_equal(true)
```

</details>

### EditorController settings integration

#### has settings_view and config fields

- has settings_view and config fields
   - Expected: src contains `settings_view:`
   - Expected: src contains `config:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has settings_view and config fields")
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("settings_view:")).to_equal(true)
expect(src.contains("config:")).to_equal(true)
```

</details>

#### has settings_open and settings_close methods

- has settings_open and settings_close methods
   - Expected: src contains `me settings_open()`
   - Expected: src contains `me settings_close()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has settings_open and settings_close methods")
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me settings_open()")).to_equal(true)
expect(src.contains("me settings_close()")).to_equal(true)
```

</details>

#### has _dispatch_settings_key method

- has _dispatch_settings_key method
   - Expected: src contains `me _dispatch_settings_key(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has _dispatch_settings_key method")
val src = read_text("src/app/editor/editor_controller.spl")
expect(src.contains("me _dispatch_settings_key(")).to_equal(true)
```

</details>

#### handle_key dispatches to settings when settings_view is active

- handle_key dispatches to settings when settings_view is active
   - Expected: src contains `if ctrl.settings_view != nil:`
   - Expected: src contains `return ctrl_dispatch_settings_key(ctrl, key)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handle_key dispatches to settings when settings_view is active")
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("if ctrl.settings_view != nil:")).to_equal(true)
expect(src.contains("return ctrl_dispatch_settings_key(ctrl, key)")).to_equal(true)
```

</details>

#### _dispatch_command_key handles settings parsed command

- _dispatch_command_key handles settings parsed command
   - Expected: src contains `parsed.name == "settings"`
   - Expected: src contains `ctrl_settings_open(ctrl)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("_dispatch_command_key handles settings parsed command")
val src = read_text("src/app/editor/editor_ctrl_core.spl")
expect(src.contains("parsed.name == \"settings\"")).to_equal(true)
expect(src.contains("ctrl_settings_open(ctrl)")).to_equal(true)
```

</details>

### TUI settings rendering

#### _tui_render_settings exists in tui_shell.spl

- _tui_render_settings exists in tui_shell.spl
   - Expected: src contains `fn _tui_render_settings(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("_tui_render_settings exists in tui_shell.spl")
val src = read_text("src/app/editor/tui_shell_panels.spl")
expect(src.contains("fn _tui_render_settings(")).to_equal(true)
```

</details>

#### tui_render_frame checks settings_view before editor rendering

- tui_render_frame checks settings_view before editor rendering
   - Expected: src contains `if ctrl.settings_view != nil:`
   - Expected: src contains `_tui_render_settings(ctrl, zones)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tui_render_frame checks settings_view before editor rendering")
val src = read_text("src/app/editor/tui_shell.spl")
expect(src.contains("if ctrl.settings_view != nil:")).to_equal(true)
expect(src.contains("_tui_render_settings(ctrl, zones)")).to_equal(true)
```

</details>

### commands.spl settings command

#### parses settings command from commandline

- parses settings command from commandline
   - Expected: src contains `"settings"`
   - Expected: src contains `editor_cmd("settings")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses settings command from commandline")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"settings\"")).to_equal(true)
expect(src.contains("editor_cmd(\"settings\")")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_settings_view_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SettingsViewState class, EditorController settings integration, TUI settings rendering, commands.spl settings command.
- SettingsViewState class
- EditorController settings integration
- TUI settings rendering
- commands.spl settings command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `417af9c1ba8ded9395e29cf16ba0bc2e5a9f9cd1898a8d28fc645872bd094269`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `417af9c1ba8ded9395e29cf16ba0bc2e5a9f9cd1898a8d28fc645872bd094269`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `417af9c1ba8ded9395e29cf16ba0bc2e5a9f9cd1898a8d28fc645872bd094269`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_settings_view_spec.spl
mirror: doc/06_spec/03_system/gui/editor_settings_view_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_settings_view_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_settings_view_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_settings_view_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines SettingsViewState with all required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_view_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines required methods on SettingsViewState' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_view_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has settings_view and config fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
