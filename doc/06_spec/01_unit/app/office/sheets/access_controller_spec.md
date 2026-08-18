# Access Controller Specification

> Tests covering Calc semantic UI access controller.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Access Controller Specification

## Scenarios

### Calc semantic UI access controller

#### exposes stable Calc cells and controls through simple.access/v1

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
val snapshot = controller.snapshot()

expect(snapshot.protocol_version).to_equal(1)
expect(snapshot.active_surface).to_equal("main")
expect(snapshot.surfaces[0].app_id).to_equal("office.calc")
expect(ui_access_find_node(snapshot, "main#cell_A1").canonical_id).to_equal("main#cell_A1")
expect(ui_access_find_node(snapshot, "main#formula_input").canonical_id).to_equal("main#formula_input")
expect(ui_access_find_nodes(snapshot, "main", "cell", "", 10).len()).to_equal(10)
```

</details>

#### renders the established full 20 by 30 sheet viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
val snapshot = controller.snapshot()
val screen = controller.tui_text()
val lines = screen.split("\n")

expect(ui_access_find_node(snapshot, "main#cell_T30").canonical_id).to_equal("main#cell_T30")
expect(lines.len()).to_equal(37)
for line in lines:
    expect(line.len()).to_equal(124)
```

</details>

#### selects, types, commits, and exposes independent calculated post-state

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
expect(controller.act(calc_access_cell_id("A1"), "select", "", "set-a1").ok).to_be(true)
expect(controller.act(calc_access_formula_input_id(), "type_text", "6", "type-a1").ok).to_be(true)
expect(controller.act(calc_access_confirm_edit_id(), "invoke", "", "commit-a1").ok).to_be(true)

expect(controller.act(calc_access_cell_id("A2"), "select", "", "set-a2").ok).to_be(true)
expect(controller.act(calc_access_formula_input_id(), "type_text", "8", "type-a2").ok).to_be(true)
expect(controller.act(calc_access_confirm_edit_id(), "invoke", "", "commit-a2").ok).to_be(true)

expect(controller.act(calc_access_cell_id("B1"), "select", "", "set-b1").ok).to_be(true)
expect(controller.act(calc_access_formula_input_id(), "type_text", "=A1*A2", "type-b1").ok).to_be(true)
expect(controller.act(calc_access_confirm_edit_id(), "invoke", "", "commit-b1").ok).to_be(true)

expect(controller.act(calc_access_cell_id("C1"), "select", "", "set-c1").ok).to_be(true)
expect(controller.act(calc_access_formula_input_id(), "type_text", "=AVG(A1:A2)", "type-c1").ok).to_be(true)
expect(controller.act(calc_access_confirm_edit_id(), "invoke", "", "commit-c1").ok).to_be(true)

val post = controller.snapshot()
expect(ui_access_find_node(post, "main#cell_B1").text_value).to_equal("48")
expect(ui_access_find_node(post, "main#cell_C1").text_value).to_equal("7")
expect(controller.tui_text()).to_contain("48")
expect(controller.tui_text()).to_contain("7")
```

</details>

#### keeps correlated newest-first history bounded to 64 events

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
var i = 0
while i < 40:
    val request_id = "select-" + i.to_text()
    controller.act(calc_access_cell_id("A1"), "select", "", request_id)
    i = i + 1

val history = controller.history("main", 100)
expect(history.len()).to_equal(64)
expect(history[0].payload).to_contain("request_id=select-39")
expect(history[1].payload).to_contain("request_id=select-39")
expect(history[0].sequence).to_be_greater_than(history[63].sequence)
```

</details>

#### rejects unsupported actions without mutating spreadsheet content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
val result = controller.act(calc_access_cell_id("A1"), "delete_everything", "", "bad-action")

expect(result.ok).to_equal(false)
expect(result.code).to_equal("unsupported_action")
val cell = ui_access_find_node(controller.snapshot(), "main#cell_A1")
expect(cell.text_value).to_equal("")
```

</details>

#### rejects malformed formulas without replacing the current cell

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
expect(controller.act(calc_access_formula_input_id(), "type_text", "=AVG(", "bad-formula-input").ok).to_equal(true)
val result = controller.act(calc_access_confirm_edit_id(), "invoke", "", "bad-formula-commit")

expect(result.ok).to_equal(false)
expect(result.code).to_equal("malformed_formula")
expect(ui_access_find_node(controller.snapshot(), "main#cell_A1").text_value).to_equal("")
```

</details>

#### applies shared UISession events to the authoritative sheet

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
controller.apply_ui_event(UIEvent.FocusEvent(target_id: "cell_A1", kind: "focus"))
controller.apply_ui_event(UIEvent.InputChange(target_id: "formula_input", value: "6"))
controller.apply_ui_event(UIEvent.Action(name: "invoke"))

expect(ui_access_find_node(controller.snapshot(), "main#cell_A1").text_value).to_equal("6")
```

</details>

#### publishes every advertised viewport cell to the live session

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
val session = UISession.new(controller.ui_tree())
val live = session.access_snapshot()

# T30 proves the live protocol tree, not merely the controller's
# private snapshot, exposes the far end of the full 20 by 30 grid.
expect(ui_access_find_node(live, "main#cell_A1").canonical_id).to_equal("main#cell_A1")
expect(ui_access_find_node(live, "main#cell_T30").canonical_id).to_equal("main#cell_T30")
```

</details>

#### incrementally refreshes the stable live tree after select type and commit

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
val session = UISession.new(controller.ui_tree())

controller.apply_ui_event_to_session(session, UIEvent.FocusEvent(target_id: "cell_B2", kind: "focus"))
controller.apply_ui_event_to_session(session, UIEvent.InputChange(target_id: "formula_input", value: "42"))
controller.apply_ui_event_to_session(session, UIEvent.Action(name: "invoke"))

val live = session.access_snapshot()
expect(ui_access_find_node(live, "main#cell_B2").selected).to_equal(true)
expect(ui_access_find_node(live, "main#cell_B2").text_value).to_equal("42")
expect(ui_access_find_node(live, "main#formula_input").text_value).to_equal("42")
# Far cells remain in this same long-lived UISession tree; this proves
# the refresh did not replace it with a compact/action-only projection.
expect(ui_access_find_node(live, "main#cell_T30").canonical_id).to_equal("main#cell_T30")
```

</details>

#### uses the same authoritative session for terminal bytes and UI access

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
val session = UISession.new(controller.ui_tree())

# TUI typing selects A1's formula field, then commits into the live
# semantic tree; no parallel workbook/session is involved.
expect(controller.apply_terminal_byte(session, 54, 0)).to_equal(0)
expect(controller.apply_terminal_byte(session, 13, 0)).to_equal(0)

val live = session.access_snapshot()
expect(ui_access_find_node(live, "main#cell_A1").text_value).to_equal("6")
```

</details>

#### rebuilds the shared viewport tree when terminal navigation scrolls

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controller = calc_access_controller_new()
val session = UISession.new(controller.ui_tree())
controller.apply_ui_event_to_session(session, UIEvent.FocusEvent(target_id: "cell_A30", kind: "focus"))
expect(controller.apply_terminal_byte(session, 27, 0)).to_equal(1)
expect(controller.apply_terminal_byte(session, 91, 1)).to_equal(2)
expect(controller.apply_terminal_byte(session, 66, 2)).to_equal(0)

val live = session.access_snapshot()
expect(ui_access_find_node(live, "main#cell_A31").canonical_id).to_equal("main#cell_A31")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/access_controller_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Calc semantic UI access controller.
- Calc semantic UI access controller

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
