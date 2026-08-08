# Ui Access Protocol Specification

> <details>

<!-- sdn-diagram:id=ui_access_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_protocol_spec -> std
ui_access_protocol_spec -> common
ui_access_protocol_spec -> nogc_sync_mut
ui_access_protocol_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Protocol Specification

## Scenarios

### ui_access_protocol feature spec

#### REQ-UAP-001 and REQ-UAP-004 expose a canonical multi-surface snapshot

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val snapshot = session.access_snapshot()
expect(snapshot.protocol_version).to_equal(1)
expect(snapshot.surfaces.len()).to_equal(2)
expect(snapshot.active_surface).to_equal("popup")
```

</details>

#### REQ-UAP-002 uses readable canonical node ids

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_access_canonical_id("popup", "ok_btn")).to_equal("popup#ok_btn")
```

</details>

#### REQ-UAP-007 and REQ-UAP-008 record recent surface-scoped history

1. session dispatch
   - Expected: popup_events[0].surface_id equals `popup`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
session.dispatch(UIEvent.Action(name: "ok"))
val popup_events = session.access_recent_surface_events("popup", 10)
expect(popup_events.len()).to_be_greater_than(0)
expect(popup_events[0].surface_id).to_equal("popup")
```

</details>

#### REQ-UAP-018 persists history and searchable nodes when a store is attached

1. var session =  session with popup

2. var store = UiAccessStore memory

3. session attach access store

4. session dispatch
   - Expected: persisted_events[0].surface_id equals `popup`
   - Expected: persisted_nodes.len() equals `1`
   - Expected: persisted_nodes[0].canonical_id equals `popup#ok_btn`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _session_with_popup()
var store = UiAccessStore.memory()?
session.attach_access_store(store)
session.dispatch(UIEvent.Action(name: "ok"))
val persisted_events = session.access_persisted_events("popup", 10)?
expect(persisted_events.len()).to_be_greater_than(0)
expect(persisted_events[0].surface_id).to_equal("popup")
val persisted_nodes = session.access_search_nodes("popup", "button", "OK", 10)?
expect(persisted_nodes.len()).to_equal(1)
expect(persisted_nodes[0].canonical_id).to_equal("popup#ok_btn")
```

</details>

#### REQ-UAP-019 enriches live surfaces with registry window metadata without persisting runtime handles

1. var session =  session with popup

2. session bind window surface
   - Expected: snapshot.surfaces.len() equals `2`
   - Expected: popup_window_id equals `55`
   - Expected: popup_app_id equals `app.popup`

3. var store = UiAccessStore memory

4. session attach access store
   - Expected: persisted_window_id equals ``


<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _session_with_popup()
session.bind_window_surface("55", "popup", 5055, "app.popup", "Popup Window")
val snapshot = session.access_snapshot()
expect(snapshot.surfaces.len()).to_equal(2)
var popup_window_id = ""
var popup_app_id = ""
for surface in snapshot.surfaces:
    if surface.surface_id == "popup":
        popup_window_id = surface.window_id
        popup_app_id = surface.app_id
expect(popup_window_id).to_equal("55")
expect(popup_app_id).to_equal("app.popup")
var store = UiAccessStore.memory()?
session.attach_access_store(store)
val persisted_surfaces = store.list_surfaces()?
var persisted_window_id = "__missing__"
for surface in persisted_surfaces:
    if surface.surface_id == "popup":
        persisted_window_id = surface.window_id
expect(persisted_window_id).to_equal("")
```

</details>

#### REQ-UAP-010 and REQ-UAP-013 expose declarative observe/state/query/ensure helpers over canonical ids

<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val server = OsMcpServer.new(VfsManager.new(), CliGuiBridge.new(session))
val observe = server.dispatch("ui_access_observe", "{\"canonical_id\":\"popup#ok_btn\"}")
expect(observe).to_contain("\"canonical_id\":\"popup#ok_btn\"")
val state = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"invoke\",\"state_value\":\"true\"}"
)
expect(state).to_contain("ok: state invoke=true -> click_ok_btn")
val query = server.dispatch(
    "ui_access_query",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"text\":\"OK\",\"focused_only\":\"false\",\"limit\":\"1\"}"
)
expect(query).to_contain("\"match_count\":1")
expect(query).to_contain("\"canonical_id\":\"popup#ok_btn\"")
val ensure = server.dispatch(
    "ui_access_ensure",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"text\":\"OK\",\"expectation\":\"match_count\",\"expected_value\":\"1\",\"limit\":\"1\"}"
)
expect(ensure).to_contain("\"satisfied\":true")
expect(ensure).to_contain("\"match_count\":1")
```

</details>

#### REQ-UAP-020 and REQ-UAP-021 expose typed value reads and writes only for input, textfield, and textarea nodes

<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_value_nodes()
val server = OsMcpServer.new(VfsManager.new(), CliGuiBridge.new(session))
val input_write = server.dispatch(
    "ui_access_value",
    "{\"canonical_id\":\"main#name_input\",\"value\":\"Ada Lovelace\"}"
)
expect(input_write).to_contain("ok")
val input_read = server.dispatch("ui_access_value", "{\"canonical_id\":\"main#name_input\"}")
expect(input_read).to_contain("main#name_input")
expect(input_read).to_contain("Ada Lovelace")
val textfield_read = server.dispatch("ui_access_value", "{\"canonical_id\":\"main#email_field\"}")
expect(textfield_read).to_contain("ada@example.com")
val textarea_write = server.dispatch(
    "ui_access_value",
    "{\"canonical_id\":\"main#notes_area\",\"value\":\"Updated notes\"}"
)
expect(textarea_write).to_contain("ok")
val textarea_read = server.dispatch("ui_access_value", "{\"canonical_id\":\"main#notes_area\"}")
expect(textarea_read).to_contain("Updated notes")
val unsupported = server.dispatch("ui_access_value", "{\"canonical_id\":\"main#submit_btn\"}")
expect(unsupported).to_contain("unsupported")
```

</details>

#### REQ-UAP-022 and REQ-UAP-023 expose additive adapter envelopes and semantic vision probes

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val server = OsMcpServer.new(VfsManager.new(), CliGuiBridge.new(session))
val adapter = server.dispatch("ui_access_adapter_snapshot", "{\"surface_id\":\"popup\"}")
expect(adapter).to_contain("\"source_kind\":\"session\"")
expect(adapter).to_contain("\"surface_id\":\"popup\"")
expect(adapter).to_contain("\"issues\":[]")
val probe = server.dispatch("ui_access_visual_probe", "{\"surface_id\":\"popup\"}")
expect(probe).to_contain("\"active_surface\":\"popup\"")
expect(probe).to_contain("\"captured\":false")
expect(probe).to_contain("\"mark_id\":\"mark_1\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/ui_access_protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui_access_protocol feature spec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
