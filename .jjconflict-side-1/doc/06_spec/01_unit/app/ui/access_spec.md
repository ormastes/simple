# Access Specification

> <details>

<!-- sdn-diagram:id=access_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=access_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

access_spec -> std
access_spec -> common
access_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=access_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Access Specification

## Scenarios

### ui_access_canonical_id

#### joins surface and widget ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_access_canonical_id("main", "submit_btn")).to_equal("main#submit_btn")
```

</details>

### ui_access_snapshot_from_state

#### builds a snapshot for the main surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
val snapshot = ui_access_snapshot_from_state(session.current_state(), [])
expect(snapshot.protocol_version).to_equal(1)
expect(snapshot.surfaces.len()).to_equal(1)
expect(snapshot.surfaces[0].surface_id).to_equal("main")
expect(snapshot.nodes.len()).to_be_greater_than(0)
```

</details>

### ui_access_find_nodes

#### finds nodes by kind and text

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
val snapshot = session.access_snapshot()
val by_kind = ui_access_find_nodes(snapshot, "main", "button", "", false)
expect(by_kind.len()).to_equal(1)
expect(by_kind[0].widget_id).to_equal("submit_btn")
val by_text = ui_access_find_nodes(snapshot, "", "", "hello", false)
expect(by_text.len()).to_be_greater_than(0)
```

</details>

#### finds only focused nodes when requested

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
val snapshot = session.access_snapshot()
val focused = ui_access_find_nodes(snapshot, "main", "", "", true)
expect(focused.len()).to_equal(1)
expect(focused[0].focused).to_equal(true)
```

</details>

### ui_access_ensure_result

#### evaluates existence, absence, and match_count expectations

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
val snapshot = session.access_snapshot()
val exists = ui_access_ensure_result(snapshot, "main", "", "button", "Submit", false, 10, "exists", "")
expect(exists.satisfied).to_equal(true)
val absent = ui_access_ensure_result(snapshot, "main", "", "button", "Missing", false, 10, "absent", "")
expect(absent.satisfied).to_equal(true)
val count = ui_access_ensure_result(snapshot, "main", "", "button", "Submit", false, 10, "match_count", "1")
expect(count.satisfied).to_equal(true)
```

</details>

#### evaluates focused and enabled expectations against matched nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
val snapshot = session.access_snapshot()
val focused = ui_access_ensure_result(snapshot, "main", "", "", "Submit", true, 10, "focused", "")
expect(focused.satisfied).to_equal(true)
val enabled = ui_access_ensure_result(snapshot, "main", "main#submit_btn", "", "", false, 10, "enabled", "")
expect(enabled.satisfied).to_equal(true)
```

</details>

### ui_access_resolve_action_name

#### keeps explicit node actions and maps semantic aliases to targeted actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
val snapshot = session.access_snapshot()
expect(ui_access_resolve_action_name(snapshot, "main#submit_btn", "submit")).to_equal("submit")
expect(ui_access_resolve_action_name(snapshot, "main#submit_btn", "invoke")).to_equal("click_submit_btn")
expect(ui_access_resolve_action_name(snapshot, "main#submit_btn", "focus")).to_equal("focus_submit_btn")
```

</details>

### ui_access_value

#### reads typed values only from value-bearing nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
val snapshot = session.access_snapshot()
val input = ui_access_find_nodes(snapshot, "main", "textfield", "", false)[0]
expect(ui_access_supports_value(input)).to_equal(true)
expect(ui_access_node_value(input)).to_equal("Ada")
val button = ui_access_find_nodes(snapshot, "main", "button", "", false)[0]
expect(ui_access_supports_value(button)).to_equal(false)
expect(ui_access_node_value(button)).to_be_nil()
val value_json = ui_access_value_to_json(snapshot, "main#name_input")
expect(value_json).to_contain("\"canonical_id\":\"main#name_input\"")
expect(value_json).to_contain("\"value\":\"Ada\"")
```

</details>

### UISession access history

#### records dispatched action events

1. session dispatch
   - Expected: events.len() equals `1`
   - Expected: events[0].event_kind equals `action`
   - Expected: events[0].payload equals `submit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _demo_session()
session.dispatch(UIEvent.Action(name: "submit"))
val events = session.access_recent_events(5)
expect(events.len()).to_equal(1)
expect(events[0].event_kind).to_equal("action")
expect(events[0].payload).to_equal("submit")
```

</details>

#### records surface scoped tree updates

1. var session =  demo session
2. session set active surface
3. column
4. session update surface tree
   - Expected: events[0].surface_id equals `popup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _demo_session()
val popup_root = text_widget("popup_text", "Popup")
val popup_tree = build_tree(popup_root)
val popup_handle = session.open_surface("popup", popup_tree)
session.set_active_surface("popup")
val popup_updated = build_tree(
    column("popup_root").child(text_widget("popup_text", "Popup Updated"))
)
session.update_surface_tree(popup_handle, popup_updated)
val events = session.access_recent_surface_events("popup", 10)
expect(events.len()).to_be_greater_than(0)
expect(events[0].surface_id).to_equal("popup")
```

</details>

### UISession persisted access

#### reads persisted snapshot nodes and events after attaching a store

1. var session =  demo session
2. var store = UiAccessStore memory
3. session attach access store
4. session dispatch
   - Expected: persisted_events[0].surface_id equals `main`
   - Expected: persisted_nodes.len() equals `1`
   - Expected: persisted_nodes[0].canonical_id equals `main#submit_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _demo_session()
var store = UiAccessStore.memory()?
session.attach_access_store(store)
session.dispatch(UIEvent.Action(name: "submit"))
val persisted_events = session.access_persisted_events("main", 10)?
expect(persisted_events.len()).to_be_greater_than(0)
expect(persisted_events[0].surface_id).to_equal("main")
val persisted_nodes = session.access_search_nodes("main", "button", "submit", 10)?
expect(persisted_nodes.len()).to_equal(1)
expect(persisted_nodes[0].canonical_id).to_equal("main#submit_btn")
```

</details>

#### enriches live snapshots from the window-surface registry without persisting runtime window ids

1. var session =  demo session
2. session bind window surface
   - Expected: live_snapshot.surfaces.len() equals `1`
   - Expected: live_snapshot.surfaces[0].window_id equals `77`
   - Expected: live_snapshot.surfaces[0].app_id equals `app.demo`
3. var store = UiAccessStore memory
4. session attach access store
   - Expected: persisted_surfaces.len() equals `1`
   - Expected: persisted_surfaces[0].window_id equals ``
   - Expected: persisted_surfaces[0].app_id equals `app.demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _demo_session()
session.bind_window_surface("77", "main", 4242, "app.demo", "Demo Window")
val live_snapshot = session.access_snapshot()
expect(live_snapshot.surfaces.len()).to_equal(1)
expect(live_snapshot.surfaces[0].window_id).to_equal("77")
expect(live_snapshot.surfaces[0].app_id).to_equal("app.demo")
var store = UiAccessStore.memory()?
session.attach_access_store(store)
val persisted_surfaces = store.list_surfaces()?
expect(persisted_surfaces.len()).to_equal(1)
expect(persisted_surfaces[0].window_id).to_equal("")
expect(persisted_surfaces[0].app_id).to_equal("app.demo")
```

</details>

### ui_access history bounds

#### keeps recent event history bounded

1. events = ui access record action
   - Expected: events.len() equals `200`
   - Expected: events[0].sequence equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var events: [UiAccessEvent] = []
var seq = 0
while seq < 205:
    seq = seq + 1
    events = ui_access_record_action(events, seq, "main", "submit_btn", "action", "submit")
expect(events.len()).to_equal(200)
expect(events[0].sequence).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/access_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui_access_canonical_id
- ui_access_snapshot_from_state
- ui_access_find_nodes
- ui_access_ensure_result
- ui_access_resolve_action_name
- ui_access_value
- UISession access history
- UISession persisted access
- ui_access history bounds

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
