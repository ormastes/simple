# Typed Action Specification

> 1. expect a to wire

<!-- sdn-diagram:id=typed_action_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=typed_action_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

typed_action_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=typed_action_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Action Specification

## Scenarios

### CommonAction.to_wire

#### Save returns save

1. expect a to wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = CommonAction.Save
expect a.to_wire() to_equal "save"
```

</details>

#### Cancel returns cancel

1. expect a to wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = CommonAction.Cancel
expect a.to_wire() to_equal "cancel"
```

</details>

#### Confirm returns confirm

1. expect a to wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = CommonAction.Confirm
expect a.to_wire() to_equal "confirm"
```

</details>

#### Dismiss returns dismiss

1. expect a to wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = CommonAction.Dismiss
expect a.to_wire() to_equal "dismiss"
```

</details>

#### Back returns back

1. expect a to wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = CommonAction.Back
expect a.to_wire() to_equal "back"
```

</details>

#### Search returns search

1. expect a to wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = CommonAction.Search
expect a.to_wire() to_equal "search"
```

</details>

#### ToggleSidebar returns toggle_sidebar

1. expect a to wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = CommonAction.ToggleSidebar
expect a.to_wire() to_equal "toggle_sidebar"
```

</details>

### Action.into_wire_name

#### Builtin Save returns save

1. var a = Action Builtin
2. expect a into wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Action.Builtin(action: CommonAction.Save)
expect a.into_wire_name() to_equal "save"
```

</details>

#### Builtin Cancel returns cancel

1. var a = Action Builtin
2. expect a into wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Action.Builtin(action: CommonAction.Cancel)
expect a.into_wire_name() to_equal "cancel"
```

</details>

#### Custom open_file returns open_file

1. var a = Action Custom
2. expect a into wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Action.Custom(name: "open_file")
expect a.into_wire_name() to_equal "open_file"
```

</details>

#### Custom empty string returns empty string

1. var a = Action Custom
2. expect a into wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Action.Custom(name: "")
expect a.into_wire_name() to_equal ""
```

</details>

### ui_event_action

#### Builtin Cancel produces UIEvent.Action with name cancel

1. var a = Action Builtin
2. var ev = ui event action
3. UIEvent Action


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Action.Builtin(action: CommonAction.Cancel)
var ev = ui_event_action(a)
match ev:
    UIEvent.Action(name):
        expect name to_equal "cancel"
    _:
        expect "wrong variant" to_equal "UIEvent.Action"
```

</details>

#### Custom save produces UIEvent.Action with name save

1. var a = Action Custom
2. var ev = ui event action
3. UIEvent Action


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Action.Custom(name: "save")
var ev = ui_event_action(a)
match ev:
    UIEvent.Action(name):
        expect name to_equal "save"
    _:
        expect "wrong variant" to_equal "UIEvent.Action"
```

</details>

### app-defined IntoAction

#### AppAction.OpenFile routes to open_file via into_action

1. var a = app into action
2. expect a into wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = AppAction.OpenFile
var a = app.into_action()
expect a.into_wire_name() to_equal "open_file"
```

</details>

#### AppAction.CloseTab routes to close_tab via into_action

1. var a = app into action
2. expect a into wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = AppAction.CloseTab
var a = app.into_action()
expect a.into_wire_name() to_equal "close_tab"
```

</details>

### CommonAction impl IntoAction

#### CommonAction.Save into_action returns Action.Builtin with save wire name

1. var a = c into action
2. expect a into wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = CommonAction.Save
var a = c.into_action()
expect a.into_wire_name() to_equal "save"
```

</details>

### with_on_typed_action

#### Custom action sets same handler_id as with_on_action

1. var base node = button
2. var typed node = with on typed action
3. var direct node = with on action
4. expect typed node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base_node = button("ta_btn_1", "Click", "x")
var typed_node = with_on_typed_action(base_node, Action.Custom(name: "x"))
var direct_node = with_on_action(base_node, "x")
expect typed_node.get_prop("on_action") to_equal direct_node.get_prop("on_action")
```

</details>

#### Builtin Save sets handler_id save

1. var base node = button
2. var typed node = with on typed action
3. expect typed node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base_node = button("ta_btn_2", "Save", "save")
var typed_node = with_on_typed_action(base_node, Action.Builtin(action: CommonAction.Save))
expect typed_node.get_prop("on_action") to_equal "save"
```

</details>

#### with_on_typed_action is wire-identical to with_on_action for same name

1. var base node = button
2. var a = Action Custom
3. var typed node = with on typed action
4. var direct node = with on action
5. expect typed node get prop


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var base_node = button("ta_btn_3", "Cancel", "cancel")
var a = Action.Custom(name: "my_action")
var typed_node = with_on_typed_action(base_node, a)
var direct_node = with_on_action(base_node, "my_action")
expect typed_node.get_prop("on_action") to_equal direct_node.get_prop("on_action")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/typed_action_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CommonAction.to_wire
- Action.into_wire_name
- ui_event_action
- app-defined IntoAction
- CommonAction impl IntoAction
- with_on_typed_action

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
