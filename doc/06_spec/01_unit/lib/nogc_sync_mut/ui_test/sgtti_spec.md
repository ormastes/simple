# Sgtti Specification

> <details>

<!-- sdn-diagram:id=sgtti_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sgtti_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sgtti_spec -> std
sgtti_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sgtti_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sgtti Specification

## Scenarios

### SGTTI UI test driver

#### finds an element by canonical id

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
val node = driver.get_element("surface:main#button_ok").unwrap()
expect(node.widget_id).to_equal("button_ok")
```

</details>

#### finds an element by widget id

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
val node = driver.get_element("name_input").unwrap()
expect(node.canonical_id).to_equal("surface:main#name_input")
```

</details>

#### returns all elements

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.from_snapshot(_sgtti_fixture_snapshot())
val nodes = driver.get_elements().unwrap()
expect(nodes.len()).to_equal(2)
```

</details>

#### delegates filtered node queries to WinText

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
val nodes = driver.find_nodes("surface:main", "input", "Ada", 10).unwrap()
expect(nodes.len()).to_equal(1)
expect(nodes[0].widget_id).to_equal("name_input")
```

</details>

#### checks visibility, focus, enabled, selected, existence, and text

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
expect(driver.check_exists("button_ok").unwrap()).to_equal(true)
expect(driver.check_visible("button_ok").unwrap()).to_equal(true)
expect(driver.check_focused("button_ok").unwrap()).to_equal(false)
expect(driver.check_enabled("button_ok").unwrap()).to_equal(true)
expect(driver.check_selected("button_ok").unwrap()).to_equal(false)
expect(driver.check_text("button_ok", "primary").unwrap()).to_equal(true)
```

</details>

#### routes click and type_text actions

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
expect(driver.click("button_ok").unwrap()).to_equal(true)
expect(driver.type_text("name_input", "Grace").unwrap()).to_equal(true)
```

</details>

#### reports missing and unsupported targets

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = SgttiTestDriver.new(_sgtti_fixture_snapshot())
expect(driver.check_exists("missing").unwrap()).to_equal(false)
expect(driver.get_element("missing").is_err()).to_equal(true)
expect(driver.click("name_input").is_err()).to_equal(true)
```

</details>

#### expands ui test target config

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_test_targets(UI_TEST_TARGET_TUI).len()).to_equal(1)
expect(ui_test_targets(UI_TEST_TARGET_TUI)[0]).to_equal(UI_TEST_TARGET_TUI)
expect(ui_test_targets(UI_TEST_TARGET_GUI)[0]).to_equal(UI_TEST_TARGET_GUI)
expect(ui_test_targets(UI_TEST_TARGET_BOTH).len()).to_equal(2)
expect(ui_test_targets(UI_TEST_TARGET_BOTH)[0]).to_equal(UI_TEST_TARGET_TUI)
expect(ui_test_targets(UI_TEST_TARGET_BOTH)[1]).to_equal(UI_TEST_TARGET_GUI)
expect(ui_test_targets("unknown").len()).to_equal(0)
```

</details>

#### passes parity when tui and gui snapshots agree

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui = SgttiTestDriver.new(_sgtti_parity_snapshot("tui", true, false, true, false))
val gui = SgttiTestDriver.new(_sgtti_parity_snapshot("gui", true, false, true, false))
val result = sgtti_parity_check(tui, gui, "shared")

expect(result.ok).to_equal(true)
expect(result.tui_found).to_equal(true)
expect(result.gui_found).to_equal(true)
expect(result.visible_match).to_equal(true)
expect(result.focused_match).to_equal(true)
expect(result.enabled_match).to_equal(true)
expect(result.selected_match).to_equal(true)
```

</details>

#### converts TUI UIState onto SGTTI and shares a parity body with GUI

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = _sgtti_tui_state()
val snapshot = sgtti_snapshot_from_tui_state(state, 1000, 5000, 1000)
val tui = SgttiTestDriver.new(snapshot)
val tui_from_state = SgttiTestDriver.from_tui_state(state, 1000, 5000, 1000)
val gui = SgttiTestDriver.new(_sgtti_gui_button_snapshot())

expect(snapshot.access.active_surface).to_equal("main")
expect(tui.get_element("shared_text").unwrap().text_value).to_equal("Shared UI")
expect(tui_from_state.check_exists("shared_text").unwrap()).to_equal(true)
val result = _sgtti_shared_text_parity(tui, gui)
expect(result.ok).to_equal(true)
expect(tui.check_text("shared_text", "Shared UI").unwrap()).to_equal(true)
expect(gui.check_text("shared_text", "Shared UI").unwrap()).to_equal(true)
```

</details>

#### builds a headless GUI snapshot with one helper call

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = gui_test_snapshot("Settings", 12, 24, 320, 200, 2000, 2000)
val driver = SgttiTestDriver.new(snapshot)
val default_snapshot = gui_test_snapshot_default("Terminal")

expect(snapshot.access.nodes.len()).to_equal(1)
expect(snapshot.access.nodes[0].kind).to_equal("compositor_window")
expect(snapshot.access.nodes[0].text_value).to_equal("Settings")
expect(driver.check_text("compositor:1#root", "Settings").unwrap()).to_equal(true)
expect(default_snapshot.access.nodes[0].text_value).to_equal("Terminal")
```

</details>

#### fails parity on divergent state or missing targets

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tui = SgttiTestDriver.new(_sgtti_parity_snapshot("tui", true, false, true, false))
val gui = SgttiTestDriver.new(_sgtti_parity_snapshot("gui", false, false, true, false))
val mismatch = sgtti_parity_check(tui, gui, "shared")
val missing = sgtti_parity_check(tui, gui, "missing")

expect(mismatch.ok).to_equal(false)
expect(mismatch.visible_match).to_equal(false)
expect(mismatch.focused_match).to_equal(true)
expect(missing.ok).to_equal(false)
expect(missing.tui_found).to_equal(false)
expect(missing.gui_found).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/ui_test/sgtti_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SGTTI UI test driver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
