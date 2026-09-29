# Typed Action Specification

> Tests covering CommonAction.to_wire, Action.into_wire_name, ui_event_action, app-defined IntoAction, CommonAction impl IntoAction, with_on_typed_action.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed Action Specification

## Scenarios

### CommonAction.to_wire

#### Save returns save

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Save returns save


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Save returns save")
var a = CommonAction.Save
expect a.to_wire() to_equal "save"
```

</details>

#### Cancel returns cancel

- Cancel returns cancel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Cancel returns cancel")
var a = CommonAction.Cancel
expect a.to_wire() to_equal "cancel"
```

</details>

#### Confirm returns confirm

- Confirm returns confirm


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Confirm returns confirm")
var a = CommonAction.Confirm
expect a.to_wire() to_equal "confirm"
```

</details>

#### Dismiss returns dismiss

- Dismiss returns dismiss


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Dismiss returns dismiss")
var a = CommonAction.Dismiss
expect a.to_wire() to_equal "dismiss"
```

</details>

#### Back returns back

- Back returns back


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Back returns back")
var a = CommonAction.Back
expect a.to_wire() to_equal "back"
```

</details>

#### Search returns search

- Search returns search


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Search returns search")
var a = CommonAction.Search
expect a.to_wire() to_equal "search"
```

</details>

#### ToggleSidebar returns toggle_sidebar

- ToggleSidebar returns toggle_sidebar


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ToggleSidebar returns toggle_sidebar")
var a = CommonAction.ToggleSidebar
expect a.to_wire() to_equal "toggle_sidebar"
```

</details>

### Action.into_wire_name

#### Builtin Save returns save

- Builtin Save returns save


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Builtin Save returns save")
var a = Action.Builtin(action: CommonAction.Save)
expect a.into_wire_name() to_equal "save"
```

</details>

#### Builtin Cancel returns cancel

- Builtin Cancel returns cancel


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Builtin Cancel returns cancel")
var a = Action.Builtin(action: CommonAction.Cancel)
expect a.into_wire_name() to_equal "cancel"
```

</details>

#### Custom open_file returns open_file

- Custom open_file returns open_file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Custom open_file returns open_file")
var a = Action.Custom(name: "open_file")
expect a.into_wire_name() to_equal "open_file"
```

</details>

#### Custom empty string returns empty string

- Custom empty string returns empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Custom empty string returns empty string")
var a = Action.Custom(name: "")
expect a.into_wire_name() to_equal ""
```

</details>

### ui_event_action

#### Builtin Cancel produces UIEvent.Action with name cancel

- Builtin Cancel produces UIEvent.Action with name cancel


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Builtin Cancel produces UIEvent.Action with name cancel")
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

- Custom save produces UIEvent.Action with name save


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Custom save produces UIEvent.Action with name save")
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

- AppAction.OpenFile routes to open_file via into_action


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AppAction.OpenFile routes to open_file via into_action")
var app = AppAction.OpenFile
var a = app.into_action()
expect a.into_wire_name() to_equal "open_file"
```

</details>

#### AppAction.CloseTab routes to close_tab via into_action

- AppAction.CloseTab routes to close_tab via into_action


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AppAction.CloseTab routes to close_tab via into_action")
var app = AppAction.CloseTab
var a = app.into_action()
expect a.into_wire_name() to_equal "close_tab"
```

</details>

### CommonAction impl IntoAction

#### CommonAction.Save into_action returns Action.Builtin with save wire name

- CommonAction.Save into_action returns Action.Builtin with save wire name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CommonAction.Save into_action returns Action.Builtin with save wire name")
var c = CommonAction.Save
var a = c.into_action()
expect a.into_wire_name() to_equal "save"
```

</details>

### with_on_typed_action

#### Custom action sets same handler_id as with_on_action

- Custom action sets same handler_id as with_on_action


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Custom action sets same handler_id as with_on_action")
var base_node = button("ta_btn_1", "Click", "x")
var typed_node = with_on_typed_action(base_node, Action.Custom(name: "x"))
var direct_node = with_on_action(base_node, "x")
expect typed_node.get_prop("on_action") to_equal direct_node.get_prop("on_action")
```

</details>

#### Builtin Save sets handler_id save

- Builtin Save sets handler_id save


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Builtin Save sets handler_id save")
var base_node = button("ta_btn_2", "Save", "save")
var typed_node = with_on_typed_action(base_node, Action.Builtin(action: CommonAction.Save))
expect typed_node.get_prop("on_action") to_equal "save"
```

</details>

#### with_on_typed_action is wire-identical to with_on_action for same name

- with_on_typed_action is wire-identical to with_on_action for same name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_on_typed_action is wire-identical to with_on_action for same name")
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
| Source | `test/unit/app/ui/typed_action_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CommonAction.to_wire, Action.into_wire_name, ui_event_action, app-defined IntoAction, CommonAction impl IntoAction, with_on_typed_action.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `793ddb0c8f0a9c5e627456a7e7cb8e8536ebe8f05dbdcf5a645026da438a9f8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `793ddb0c8f0a9c5e627456a7e7cb8e8536ebe8f05dbdcf5a645026da438a9f8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `793ddb0c8f0a9c5e627456a7e7cb8e8536ebe8f05dbdcf5a645026da438a9f8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/typed_action_spec.spl
mirror: doc/06_spec/unit/app/ui/typed_action_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/typed_action_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/typed_action_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/typed_action_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Save returns save' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/typed_action_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Cancel returns cancel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/typed_action_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Confirm returns confirm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
