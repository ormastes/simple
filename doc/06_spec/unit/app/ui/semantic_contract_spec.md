# Semantic Contract Specification

> <details>

<!-- sdn-diagram:id=semantic_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semantic_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semantic_contract_spec -> std
semantic_contract_spec -> common
semantic_contract_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semantic_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Contract Specification

## Scenarios

### semantic UI contract snapshot

#### builds semantic state from the existing UI access snapshot model

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = semantic_ui_snapshot_from_state(_semantic_demo_state(), SEMANTIC_UI_STAGE_STATE, SEMANTIC_UI_STATUS_AVAILABLE)
expect(snapshot.protocol_version).to_equal(SEMANTIC_UI_PROTOCOL_VERSION)
expect(snapshot.stage).to_equal("S1")
expect(snapshot.adapter_status).to_equal("available")
expect(snapshot.state.mode).to_equal("NORMAL")
expect(snapshot.state.active_surface).to_equal("main")
expect(snapshot.state.element_count).to_be_greater_than(0)
expect(snapshot.elements.len()).to_equal(snapshot.state.element_count)
expect(snapshot.elements[0].canonical_id).to_start_with("main#")
```

</details>

#### reports unavailable semantic adapters explicitly

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = SemanticUiSnapshot.unavailable(SEMANTIC_UI_STAGE_STATE, SEMANTIC_UI_STATUS_UNAVAILABLE)
expect(snapshot.protocol_version).to_equal(SEMANTIC_UI_PROTOCOL_VERSION)
expect(snapshot.adapter_status).to_equal("semantic_adapter_unavailable")
expect(snapshot.state.element_count).to_equal(0)
expect(snapshot.elements.len()).to_equal(0)
```

</details>

#### serializes semantic snapshots into shared render snapshot envelopes

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snapshot = semantic_ui_snapshot_from_state_with_capabilities(_semantic_demo_state(), SEMANTIC_UI_STAGE_RENDERER, SEMANTIC_UI_STATUS_AVAILABLE, [Capability.Mouse])
val json = semantic_ui_snapshot_to_json(snapshot)
expect(json).to_contain("\"stage\":\"S3\"")
expect(json).to_contain("\"adapter_status\":\"available\"")
expect(json).to_contain("\"element_count\":3")
expect(json).to_contain("\"capabilities\":[")
expect(json).to_contain("\"name\":\"Mouse\"")
expect(json).to_contain("\"canonical_id\":\"main#root\"")

val envelope = semantic_ui_snapshot_transport_json(WEB_RENDER_TARGET_ELECTRON, "main", 7u64, snapshot)
expect(envelope).to_contain("\"type\":\"snapshot\"")
expect(envelope).to_contain("\"target\":\"electron\"")
expect(envelope).to_contain("\"revision\":7")
expect(envelope).to_contain("protocol_version")
```

</details>

#### carries backend capability vocabulary in semantic snapshots

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = semantic_ui_capabilities_from_backend([Capability.Mouse, Capability.Color])
expect(caps.len()).to_equal(2)
expect(caps[0].name).to_equal("Mouse")
expect(caps[0].available).to_equal(true)

val snapshot = semantic_ui_snapshot_from_state_with_capabilities(_semantic_demo_state(), SEMANTIC_UI_STAGE_STATE, SEMANTIC_UI_STATUS_AVAILABLE, [Capability.Mouse, Capability.Color])
expect(semantic_ui_has_capability(snapshot, "Mouse")).to_equal(true)
expect(semantic_ui_has_capability(snapshot, "Color")).to_equal(true)
expect(semantic_ui_has_capability(snapshot, "Images")).to_equal(false)
```

</details>

### semantic UI command contract

#### creates shared command records independent of transport

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val click = SemanticUiCommand.click("main", "submit_btn")
expect(click.command_type).to_equal("click")
expect(click.surface_id).to_equal("main")
expect(click.target_id).to_equal("submit_btn")
expect(semantic_ui_command_to_event_kind(click)).to_equal("click")

val typed = SemanticUiCommand.type_text("main", "name_input", "Grace")
expect(typed.command_type).to_equal("type")
expect(typed.value).to_equal("Grace")
expect(semantic_ui_command_to_event_kind(typed)).to_equal("input")

val key = SemanticUiCommand.key("main", "enter")
expect(key.key).to_equal("enter")
expect(semantic_ui_command_to_event_kind(key)).to_equal("key")
```

</details>

#### maps semantic commands to existing UI events

1. UIEvent InputChange
   - Expected: typed_target equals `name_input`
   - Expected: typed_value equals `Grace`

2. UIEvent FocusEvent
   - Expected: focus_target equals `submit_btn`
   - Expected: focus_kind equals `focus`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val typed = semantic_ui_command_to_event(SemanticUiCommand.type_text("main", "name_input", "Grace"))
var typed_target = ""
var typed_value = ""
match typed:
    UIEvent.InputChange(target_id, value):
        typed_target = target_id
        typed_value = value
    _:
        typed_target = "wrong-event"
        typed_value = "wrong-event"
expect(typed_target).to_equal("name_input")
expect(typed_value).to_equal("Grace")

val focus = semantic_ui_command_to_event(SemanticUiCommand.focus("main", "submit_btn"))
var focus_target = ""
var focus_kind = ""
match focus:
    UIEvent.FocusEvent(target_id, kind):
        focus_target = target_id
        focus_kind = kind
    _:
        focus_target = "wrong-event"
        focus_kind = "wrong-event"
expect(focus_target).to_equal("submit_btn")
expect(focus_kind).to_equal("focus")
```

</details>

#### records dispatch success and failure with read-after-write revision

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = SemanticUiCommand.click("main", "submit_btn")
val success = SemanticUiDispatchResult.success(command, "main#submit_btn", 4)
expect(success.ok).to_equal(true)
expect(success.affected_id).to_equal("main#submit_btn")
expect(success.snapshot_revision).to_equal(4)

val failure = SemanticUiDispatchResult.failure(command, "element_not_found", 5)
expect(failure.ok).to_equal(false)
expect(failure.reason).to_equal("element_not_found")
expect(failure.snapshot_revision).to_equal(5)
```

</details>

#### dispatches semantic commands through UISession state and access history

1. var session = UISession new
   - Expected: result.ok is true
   - Expected: result.affected_id equals `main#submit_btn`
   - Expected: result.snapshot_revision equals `1`
   - Expected: session.current_state().focused_id equals `submit_btn`
   - Expected: events.len() equals `1`
   - Expected: events[0].event_kind equals `focus_focus`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = UISession.new(_semantic_demo_state().tree)
val command = SemanticUiCommand.focus("main", "submit_btn")
val result = session.dispatch_semantic_command(command)
expect(result.ok).to_equal(true)
expect(result.affected_id).to_equal("main#submit_btn")
expect(result.snapshot_revision).to_equal(1)
expect(session.current_state().focused_id).to_equal("submit_btn")
val events = session.access_recent_events(1)
expect(events.len()).to_equal(1)
expect(events[0].event_kind).to_equal("focus_focus")
```

</details>

### semantic UI maturity stages

#### orders staged contract membership

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(semantic_ui_stage_at_least(SEMANTIC_UI_STAGE_PROTOCOL, SEMANTIC_UI_STAGE_STATE)).to_equal(true)
expect(semantic_ui_stage_at_least(SEMANTIC_UI_STAGE_RENDERER, SEMANTIC_UI_STAGE_EVENTS)).to_equal(true)
expect(semantic_ui_stage_at_least(SEMANTIC_UI_STAGE_STATE, SEMANTIC_UI_STAGE_EVENTS)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/semantic_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- semantic UI contract snapshot
- semantic UI command contract
- semantic UI maturity stages

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
