# State Event Specification

> <details>

<!-- sdn-diagram:id=state_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=state_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

state_event_spec -> std
state_event_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=state_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# State Event Specification

## Scenarios

### init_state

#### creates state with Normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
expect(state.mode_name()).to_equal("NORMAL")
```

</details>

#### sets focused_id to first widget id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
# all_widget_ids returns root first
val first_id = tree.all_widget_ids()[0]
expect(state.focused_id).to_equal(first_id)
```

</details>

### init_state_with_mode

#### sets Command mode when given command string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
expect(state.mode_name()).to_equal("COMMAND")
```

</details>

#### sets Insert mode when given insert string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "insert")
expect(state.mode_name()).to_equal("INSERT")
```

</details>

#### sets Menu mode when given menu string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "menu")
expect(state.mode_name()).to_equal("MENU")
```

</details>

#### defaults to Normal mode for unknown string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "unknown")
expect(state.mode_name()).to_equal("NORMAL")
```

</details>

### focus navigation

#### advances focused_id on FocusNext

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
val s2 = update_state(state, UIEvent.FocusNext)
# Should move from first id to second id
expect(s2.focused_id).to_equal(ids[1])
```

</details>

#### retreats focused_id on FocusPrev

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# Move forward first, then back
val s2 = update_state(state, UIEvent.FocusNext)
val s3 = update_state(s2, UIEvent.FocusPrev)
expect(s3.focused_id).to_equal(ids[0])
```

</details>

#### wraps around at end of list

- s = update state
   - Expected: s.focused_id equals `ids[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# Navigate forward through all widgets to wrap
var s = state
var i = 0
while i < ids.len():
    s = update_state(s, UIEvent.FocusNext)
    i = i + 1
# After len() FocusNext events, should wrap to first
expect(s.focused_id).to_equal(ids[0])
```

</details>

#### wraps around at beginning of list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# FocusPrev from first element should wrap to last
val s2 = update_state(state, UIEvent.FocusPrev)
expect(s2.focused_id).to_equal(ids[ids.len() - 1])
```

</details>

### quit detection

#### is_quit_event returns true for Quit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_quit_event(UIEvent.Quit)).to_equal(true)
```

</details>

#### is_quit_event returns false for FocusNext

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_quit_event(UIEvent.FocusNext)).to_equal(false)
```

</details>

#### is_quit_event returns false for KeyPress

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_quit_event(UIEvent.KeyPress(key: "q"))).to_equal(false)
```

</details>

### keypress normal mode

#### j triggers focus next

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
val s2 = update_state(state, UIEvent.KeyPress(key: "j"))
expect(s2.focused_id).to_equal(ids[1])
```

</details>

#### k triggers focus prev

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val ids = tree.all_widget_ids()
# Move forward first so we can go back
val s2 = update_state(state, UIEvent.KeyPress(key: "j"))
val s3 = update_state(s2, UIEvent.KeyPress(key: "k"))
expect(s3.focused_id).to_equal(ids[0])
```

</details>

#### colon switches to Command mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.KeyPress(key: ":"))
expect(s2.mode_name()).to_equal("COMMAND")
```

</details>

#### i switches to Insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.KeyPress(key: "i"))
expect(s2.mode_name()).to_equal("INSERT")
```

</details>

### escape key handling

#### escape in Command mode returns to Normal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
val s2 = update_state(state, UIEvent.KeyPress(key: "escape"))
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

#### escape in Insert mode returns to Normal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "insert")
val s2 = update_state(state, UIEvent.KeyPress(key: "escape"))
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

#### escape in Menu mode returns to Normal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "menu")
val s2 = update_state(state, UIEvent.KeyPress(key: "escape"))
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

### mode_name

#### returns NORMAL for Normal mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "normal")
expect(state.mode_name()).to_equal("NORMAL")
```

</details>

#### returns COMMAND for Command mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
expect(state.mode_name()).to_equal("COMMAND")
```

</details>

#### returns INSERT for Insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "insert")
expect(state.mode_name()).to_equal("INSERT")
```

</details>

#### returns MENU for Menu mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "menu")
expect(state.mode_name()).to_equal("MENU")
```

</details>

### mode switching via events

#### CommandMode event switches to Command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.CommandMode)
expect(s2.mode_name()).to_equal("COMMAND")
```

</details>

#### InsertMode event switches to Insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state(tree)
val s2 = update_state(state, UIEvent.InsertMode)
expect(s2.mode_name()).to_equal("INSERT")
```

</details>

#### NormalMode event switches to Normal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = make_test_tree()
val state = init_state_with_mode(tree, "command")
val s2 = update_state(state, UIEvent.NormalMode)
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/state_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- init_state
- init_state_with_mode
- focus navigation
- quit detection
- keypress normal mode
- escape key handling
- mode_name
- mode switching via events

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
