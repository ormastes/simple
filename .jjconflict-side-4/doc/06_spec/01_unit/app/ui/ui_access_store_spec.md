# Ui Access Store Specification

> 1. store close

<!-- sdn-diagram:id=ui_access_store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_store_spec -> std
ui_access_store_spec -> common
ui_access_store_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Store Specification

## Scenarios

### UiAccessStore

#### opens and closes a file-backed store

1. store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = UiAccessStore.open("/tmp/ui_access_store_test.sqlite")?
store.close()?
```

</details>

#### opens an in-memory store and allows schema re-initialization

1. var store = UiAccessStore memory
2. store init schema
3. store close


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = UiAccessStore.memory()?
store.init_schema()?
store.close()?
```

</details>

#### persists events and lists them newest-first

1. var store = UiAccessStore memory
2. store insert event
3. store insert event
4. store insert event
   - Expected: all_events.len() equals `3`
   - Expected: all_events[0].sequence equals `3`
   - Expected: all_events[1].sequence equals `2`
   - Expected: all_events[2].sequence equals `1`
   - Expected: main_events.len() equals `2`
   - Expected: main_events[0].surface_id equals `main`
   - Expected: main_events[0].canonical_id equals `main#submit_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = UiAccessStore.memory()?
store.insert_event(_event(1, "main", "submit_btn", "action", "click"))?
store.insert_event(_event(3, "main", "submit_btn", "action", "focus"))?
store.insert_event(_event(2, "popup", "ok_btn", "action", "click"))?
val all_events = store.list_events("", 10)?
expect(all_events.len()).to_equal(3)
expect(all_events[0].sequence).to_equal(3)
expect(all_events[1].sequence).to_equal(2)
expect(all_events[2].sequence).to_equal(1)
val main_events = store.list_events("main", 10)?
expect(main_events.len()).to_equal(2)
expect(main_events[0].surface_id).to_equal("main")
expect(main_events[0].canonical_id).to_equal("main#submit_btn")
```

</details>

#### persists a snapshot and keeps the latest current nodes

1. var store = UiAccessStore memory
2. [ surface
3.  node
4.  node
5. store persist snapshot
   - Expected: initial_surfaces.len() equals `1`
   - Expected: initial_surfaces[0].surface_id equals `main`
   - Expected: initial_surfaces[0].active is true
   - Expected: initial_nodes.len() equals `1`
   - Expected: initial_nodes[0].canonical_id equals `main#submit_btn`
   - Expected: initial_nodes[0].text equals `Submit`
   - Expected: initial_nodes[0].action_names.len() equals `2`
6.  surface
7.  surface
8.  node
9.  node
10.  node
11.  node
12. store persist snapshot
   - Expected: surfaces.len() equals `2`
   - Expected: surfaces[0].surface_id equals `main`
   - Expected: surfaces[1].surface_id equals `popup`
   - Expected: nodes.len() equals `1`
   - Expected: nodes[0].text equals `Save`
   - Expected: nodes[0].action_names.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = UiAccessStore.memory()?
val initial_snapshot = _snapshot(
    "main",
    [_surface("main", "Main", true, "root_main")],
    [
        _node("main", "root_main", "root", "Main", "Main", true, true, true, false, ["main#submit_btn"], []),
        _node("main", "submit_btn", "button", "Submit", "Submit", true, true, true, false, [], ["click", "focus"])
    ]
)
store.persist_snapshot(initial_snapshot)?
val initial_surfaces = store.list_surfaces()?
expect(initial_surfaces.len()).to_equal(1)
expect(initial_surfaces[0].surface_id).to_equal("main")
expect(initial_surfaces[0].active).to_equal(true)
val initial_nodes = store.query_nodes("main", "button", "submit", 10)?
expect(initial_nodes.len()).to_equal(1)
expect(initial_nodes[0].canonical_id).to_equal("main#submit_btn")
expect(initial_nodes[0].text).to_equal("Submit")
expect(initial_nodes[0].action_names.len()).to_equal(2)

val updated_snapshot = _snapshot(
    "main",
    [
        _surface("main", "Main", true, "root_main"),
        _surface("popup", "Popup", false, "root_popup")
    ],
    [
        _node("main", "root_main", "root", "Main", "Main", true, true, true, false, ["main#submit_btn"], []),
        _node("main", "submit_btn", "button", "Save", "Save", true, true, true, false, [], ["click", "focus"]),
        _node("popup", "root_popup", "root", "Popup", "Popup", true, false, true, false, ["popup#ok_btn"], []),
        _node("popup", "ok_btn", "button", "OK", "OK", true, false, true, false, [], ["click"])
    ]
)
store.persist_snapshot(updated_snapshot)?
val surfaces = store.list_surfaces()?
expect(surfaces.len()).to_equal(2)
expect(surfaces[0].surface_id).to_equal("main")
expect(surfaces[1].surface_id).to_equal("popup")
val nodes = store.query_nodes("main", "button", "", 10)?
expect(nodes.len()).to_equal(1)
expect(nodes[0].text).to_equal("Save")
expect(nodes[0].action_names.len()).to_equal(2)
```

</details>

#### filters persisted nodes by surface, kind, text, and limit

1. var store = UiAccessStore memory
2.  surface
3.  surface
4.  node
5.  node
6.  node
7.  node
8.  node
9. store persist snapshot
   - Expected: main_buttons.len() equals `1`
   - Expected: main_buttons[0].widget_id equals `submit_btn`
   - Expected: by_text.len() equals `1`
   - Expected: by_text[0].surface_id equals `main`
   - Expected: by_text[0].widget_id equals `title`
   - Expected: all_nodes.len() equals `5`
   - Expected: limited.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = UiAccessStore.memory()?
val snapshot = _snapshot(
    "main",
    [
        _surface("main", "Main", true, "root_main"),
        _surface("popup", "Popup", false, "root_popup")
    ],
    [
        _node("main", "root_main", "root", "Main", "Main", true, true, true, false, ["main#submit_btn"], []),
        _node("main", "submit_btn", "button", "Submit", "Submit", true, true, true, false, [], ["click", "focus"]),
        _node("main", "title", "text", "Title", "Hello Access", true, false, true, false, [], []),
        _node("popup", "root_popup", "root", "Popup", "Popup", true, false, true, false, ["popup#ok_btn"], []),
        _node("popup", "ok_btn", "button", "OK", "OK", true, false, true, false, [], ["click"])
    ]
)
store.persist_snapshot(snapshot)?
val main_buttons = store.query_nodes("main", "button", "", 10)?
expect(main_buttons.len()).to_equal(1)
expect(main_buttons[0].widget_id).to_equal("submit_btn")
val by_text = store.query_nodes("", "", "hello", 10)?
expect(by_text.len()).to_equal(1)
expect(by_text[0].surface_id).to_equal("main")
expect(by_text[0].widget_id).to_equal("title")
val all_nodes = store.query_nodes("", "", "", 10)?
expect(all_nodes.len()).to_equal(5)
val limited = store.query_nodes("", "", "", 2)?
expect(limited.len()).to_equal(2)
```

</details>

#### reopens a file-backed store and preserves current nodes and events

1. file delete
2. var first = UiAccessStore open
3. first insert event
4. [ surface
5.  node
6.  node
7. first close
8. var reopened = UiAccessStore open
   - Expected: events.len() equals `1`
   - Expected: events[0].payload equals `submit`
   - Expected: nodes.len() equals `1`
   - Expected: nodes[0].canonical_id equals `main#submit_btn`
9. reopened close
10. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/ui_access_store_reopen.sqlite"
if file_exists(db_path):
    file_delete(db_path)
var first = UiAccessStore.open(db_path)?
first.insert_event(_event(1, "main", "submit_btn", "action", "submit"))?
first.persist_snapshot(_snapshot(
    "main",
    [_surface("main", "Main", true, "root_main")],
    [
        _node("main", "root_main", "root", "Main", "Main", true, true, true, false, ["main#submit_btn"], []),
        _node("main", "submit_btn", "button", "Submit", "Submit", true, true, true, false, [], ["click"])
    ]
))?
first.close()?
var reopened = UiAccessStore.open(db_path)?
val events = reopened.list_events("main", 10)?
expect(events.len()).to_equal(1)
expect(events[0].payload).to_equal("submit")
val nodes = reopened.query_nodes("main", "button", "submit", 10)?
expect(nodes.len()).to_equal(1)
expect(nodes[0].canonical_id).to_equal("main#submit_btn")
reopened.close()?
if file_exists(db_path):
    file_delete(db_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ui_access_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UiAccessStore

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
