# Ui Access Dispatch Specification

> <details>

<!-- sdn-diagram:id=ui_access_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_dispatch_spec -> std
ui_access_dispatch_spec -> common
ui_access_dispatch_spec -> nogc_sync_mut
ui_access_dispatch_spec -> os
ui_access_dispatch_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Dispatch Specification

## Scenarios

### ui_access_protocol MCP dispatch

#### routes snapshot and surface reads through the canonical dispatcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val snapshot = server.dispatch("ui_access_snapshot", "")
expect(snapshot).to_contain("\"protocol_version\":1")
expect(snapshot).to_contain("\"popup\"")
val find = server.dispatch(
    "ui_access_find",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"text\":\"OK\",\"focused_only\":\"false\"}"
)
expect(find).to_contain("popup#ok_btn")
val surface = server.dispatch("ui_access_surface", "{\"surface_id\":\"popup\"}")
expect(surface).to_contain("\"surface_id\":\"popup\"")
expect(surface).to_contain("popup#ok_btn")
```

</details>

#### binds window metadata through the shared session registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val created = server.dispatch(
    "window_create",
    "{\"title\":\"Inspector\",\"width\":\"640\",\"height\":\"480\"}"
)
expect(created).to_contain("ok: created window")
val snapshot = server.dispatch("ui_access_snapshot", "")
expect(snapshot).to_contain("\"window_id\":\"1\"")
expect(snapshot).to_contain("\"surface_id\":\"window_1\"")
```

</details>

#### dispatches canonical actions and rejects invalid targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val action = server.dispatch(
    "ui_access_act",
    "{\"surface_id\":\"popup\",\"canonical_id\":\"popup#ok_btn\",\"action\":\"click\"}"
)
expect(action).to_contain("ok: dispatched click_ok_btn")
val alias = server.dispatch(
    "ui_access_act",
    "{\"surface_id\":\"main\",\"canonical_id\":\"main#submit_btn\",\"action\":\"submit\"}"
)
expect(alias).to_contain("ok: dispatched submit")
expect(bridge.session.active_surface()).to_equal("popup")
val history = server.dispatch("ui_access_history", "{\"surface_id\":\"popup\",\"count\":\"5\"}")
expect(history).to_contain("\"event_kind\":\"action\"")
val missing_surface = server.dispatch(
    "ui_access_act",
    "{\"surface_id\":\"missing\",\"action\":\"click\"}"
)
expect(missing_surface).to_contain("error: surface missing not found")
val missing_target = server.dispatch("ui_access_act", "{\"action\":\"click\"}")
expect(missing_target).to_contain("error: missing surface_id")
```

</details>

#### observes declarative state through snapshot, surface, node, and filtered reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val whole = server.dispatch("ui_access_observe", "{}")
expect(whole).to_contain("\"protocol_version\":1")
val surface = server.dispatch("ui_access_observe", "{\"surface_id\":\"popup\"}")
expect(surface).to_contain("\"surface_id\":\"popup\"")
val node = server.dispatch("ui_access_observe", "{\"canonical_id\":\"popup#ok_btn\"}")
expect(node).to_contain("\"canonical_id\":\"popup#ok_btn\"")
val filtered = server.dispatch(
    "ui_access_observe",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"text\":\"OK\",\"focused_only\":\"false\"}"
)
expect(filtered).to_contain("popup#ok_btn")
```

</details>

#### queries structured declarative results

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val query = server.dispatch(
    "ui_access_query",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"text\":\"OK\",\"focused_only\":\"false\",\"limit\":\"1\"}"
)
expect(query).to_contain("\"match_count\":1")
expect(query).to_contain("\"truncated\":false")
expect(query).to_contain("\"surface_id\":\"popup\"")
expect(query).to_contain("\"canonical_id\":\"popup#ok_btn\"")
val missing = server.dispatch(
    "ui_access_query",
    "{\"canonical_id\":\"popup#missing\"}"
)
expect(missing).to_contain("error: canonical node popup#missing not found")
```

</details>

#### ensures bounded declarative expectations over canonical queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val missing = server.dispatch(
    "ui_access_ensure",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"text\":\"Missing\",\"expectation\":\"absent\"}"
)
expect(missing).to_contain("\"satisfied\":true")
val focus = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"focused\",\"state_value\":\"true\"}"
)
expect(focus).to_contain("ok: state focused=true -> focus_ok_btn")
val ensured = server.dispatch(
    "ui_access_ensure",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"focused_only\":\"true\",\"expectation\":\"match_count\",\"expected_value\":\"1\",\"limit\":\"1\"}"
)
expect(ensured).to_contain("\"satisfied\":true")
expect(ensured).to_contain("\"match_count\":1")
expect(ensured).to_contain("\"canonical_id\":\"popup#ok_btn\"")
```

</details>

#### preserves focused semantics across state, observe, and query

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val empty = server.dispatch(
    "ui_access_query",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"focused_only\":\"true\",\"limit\":\"1\"}"
)
expect(empty).to_contain("\"match_count\":0")
val focus = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"focused\",\"state_value\":\"true\"}"
)
expect(focus).to_contain("ok: state focused=true -> focus_ok_btn")
val observed = server.dispatch(
    "ui_access_observe",
    "{\"canonical_id\":\"popup#ok_btn\"}"
)
expect(observed).to_contain("\"canonical_id\":\"popup#ok_btn\"")
expect(observed).to_contain("\"focused\":true")
val query = server.dispatch(
    "ui_access_query",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"focused_only\":\"true\",\"limit\":\"1\"}"
)
expect(query).to_contain("\"match_count\":1")
expect(query).to_contain("\"canonical_id\":\"popup#ok_btn\"")
```

</details>

#### reads and sets declarative state through canonical targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val read = server.dispatch("ui_access_state", "{\"canonical_id\":\"popup#ok_btn\"}")
expect(read).to_contain("\"canonical_id\":\"popup#ok_btn\"")
val read_key = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"focused\"}"
)
expect(read_key).to_contain("\"state_key\":\"focused\"")
expect(read_key).to_contain("\"state_value\":\"false\"")
val surface_read = server.dispatch(
    "ui_access_state",
    "{\"surface_id\":\"popup\",\"state_key\":\"active\"}"
)
expect(surface_read).to_contain("\"surface_id\":\"popup\"")
expect(surface_read).to_contain("\"state_value\":\"true\"")
val focus = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"focused\",\"state_value\":\"true\"}"
)
expect(focus).to_contain("ok: state focused=true -> focus_ok_btn")
val active = server.dispatch(
    "ui_access_state",
    "{\"surface_id\":\"main\",\"state_key\":\"active\",\"state_value\":\"true\"}"
)
expect(active).to_contain("ok: state active=true on main")
expect(bridge.session.active_surface()).to_equal("main")
val invoke = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"main#submit_btn\",\"state_key\":\"invoke\",\"state_value\":\"true\"}"
)
expect(invoke).to_contain("ok: state invoke=true -> click_submit_btn")
val selected_false = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"main#submit_btn\",\"state_key\":\"selected\",\"state_value\":\"false\"}"
)
expect(selected_false).to_contain("ok: state selected=false on main#submit_btn")
```

</details>

#### reads and writes typed values for value-bearing canonical nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val read = server.dispatch("ui_access_value", "{\"canonical_id\":\"main#name_input\"}")
expect(read).to_contain("\"canonical_id\":\"main#name_input\"")
expect(read).to_contain("\"value\":\"Ada\"")
val write = server.dispatch(
    "ui_access_value",
    "{\"surface_id\":\"main\",\"canonical_id\":\"main#name_input\",\"value\":\"Grace\"}"
)
expect(write).to_contain("\"value\":\"Grace\"")
val reread = server.dispatch("ui_access_value", "{\"canonical_id\":\"main#name_input\"}")
expect(reread).to_contain("\"value\":\"Grace\"")
val unsupported = server.dispatch("ui_access_value", "{\"canonical_id\":\"main#submit_btn\"}")
expect(unsupported).to_contain("error: unsupported value target main#submit_btn")
```

</details>

#### reads additive adapter snapshots and vision probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
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

#### rejects invalid declarative state transitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val unsupported = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"focused\",\"state_value\":\"false\"}"
)
expect(unsupported).to_contain("error: unsupported state transition focused=false")
val unsupported_key = server.dispatch(
    "ui_access_state",
    "{\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"bogus\"}"
)
expect(unsupported_key).to_contain("error: unsupported state key bogus")
val missing = server.dispatch("ui_access_state", "{\"state_key\":\"active\",\"state_value\":\"true\"}")
expect(missing).to_contain("error: missing surface_id")
```

</details>

#### reads persisted find and history results when a store is attached

1. var session =  session with popup
2. var store = UiAccessStore memory
3. session attach access store
4. store persist snapshot
5. session dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _session_with_popup()
var store = UiAccessStore.memory()?
session.attach_access_store(store)
store.persist_snapshot(_stored_snapshot())?
session.dispatch(UIEvent.Action(name: "submit"))
session.access_events = []
val bridge = CliGuiBridge.new(session)
val server = OsMcpServer.new(VfsManager.new(), bridge)
val find = server.dispatch(
    "ui_access_find",
    "{\"surface_id\":\"popup\",\"kind\":\"button\",\"text\":\"Stored\",\"focused_only\":\"false\"}"
)
expect(find).to_contain("popup#stored_ok_btn")
val history = server.dispatch("ui_access_history", "{\"surface_id\":\"popup\",\"count\":\"5\"}")
expect(history).to_contain("\"surface_id\":\"popup\"")
expect(history).to_contain("\"event_kind\":\"action\"")
```

</details>

#### auto-attaches a persisted store through CliGuiBridge.new when runtime path is configured

1. rt env set
2. file delete
3. var session =  session with popup
4. bridge session dispatch
5. rt env set
6. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/ui_access_bridge_auto.sqlite"
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", db_path)
if file_exists(db_path):
    file_delete(db_path)
var session = _session_with_popup()
val bridge = CliGuiBridge.new(session)
bridge.session.dispatch(UIEvent.Action(name: "submit"))
bridge.session.access_events = []
val server = OsMcpServer.new(VfsManager.new(), bridge)
val history = server.dispatch("ui_access_history", "{\"surface_id\":\"popup\",\"count\":\"5\"}")
expect(history).to_contain("\"surface_id\":\"popup\"")
expect(history).to_contain("\"event_kind\":\"action\"")
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "")
if file_exists(db_path):
    file_delete(db_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/llm/ui_access_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui_access_protocol MCP dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
