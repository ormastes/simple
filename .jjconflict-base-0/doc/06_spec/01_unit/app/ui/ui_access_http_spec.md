# Ui Access Http Specification

> 1. session current state

<!-- sdn-diagram:id=ui_access_http_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_http_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_http_spec -> std
ui_access_http_spec -> common
ui_access_http_spec -> nogc_sync_mut
ui_access_http_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_http_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Http Specification

## Scenarios

### ui_access_protocol HTTP routes

#### returns a state-derived snapshot without a session and a multi-surface snapshot with one

1. session current state
   - Expected: fallback.0 equals `200`
2. session current state
   - Expected: live.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val fallback = handle_test_request(
    "/api/test/ui/snapshot",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    nil
)
expect(fallback.0).to_equal(200)
expect(fallback.2).to_contain("\"main\"")
val live = handle_test_request(
    "/api/test/ui/snapshot",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(live.0).to_equal(200)
expect(live.2).to_contain("\"popup\"")
expect(live.2).to_contain("\"protocol_version\":1")
```

</details>

#### serves named surfaces and rejects missing ones

1. session current state
   - Expected: found.0 equals `200`
2. session current state
   - Expected: missing.0 equals `404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val found = handle_test_request(
    "/api/test/ui/surface?id=popup",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(found.0).to_equal(200)
expect(found.2).to_contain("\"surface_id\":\"popup\"")
expect(found.2).to_contain("popup#ok_btn")
val missing = handle_test_request(
    "/api/test/ui/surface?id=missing",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(missing.0).to_equal(404)
expect(missing.2).to_contain("Surface not found")
```

</details>

#### returns history for the active surface and falls back to empty without a session

1. var session =  session with popup
2. session dispatch
3. session current state
   - Expected: live.0 equals `200`
4. session current state
   - Expected: fallback.0 equals `200`
   - Expected: fallback.2 equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _session_with_popup()
session.dispatch(UIEvent.Action(name: "submit"))
val live = handle_test_request(
    "/api/test/ui/history?surface_id=popup&count=5",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(live.0).to_equal(200)
expect(live.2).to_contain("\"surface_id\":\"popup\"")
expect(live.2).to_contain("\"event_kind\":\"action\"")
val fallback = handle_test_request(
    "/api/test/ui/history?count=5",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    nil
)
expect(fallback.0).to_equal(200)
expect(fallback.2).to_equal("[]")
```

</details>

#### serves persisted history when a store is attached

1. var session =  session with popup
2. var store = UiAccessStore memory
3. session attach access store
4. session dispatch
5. session current state
   - Expected: live.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = _session_with_popup()
var store = UiAccessStore.memory()?
session.attach_access_store(store)
session.dispatch(UIEvent.Action(name: "submit"))
session.access_events = []
val live = handle_test_request(
    "/api/test/ui/history?surface_id=popup&count=5",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(live.0).to_equal(200)
expect(live.2).to_contain("\"surface_id\":\"popup\"")
expect(live.2).to_contain("\"event_kind\":\"action\"")
```

</details>

#### observes canonical nodes and rejects missing selectors

1. session current state
   - Expected: found.0 equals `200`
2. session current state
   - Expected: missing.0 equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val found = handle_test_request(
    "/api/test/ui/observe?canonical_id=popup#ok_btn",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(found.0).to_equal(200)
expect(found.2).to_contain("\"canonical_id\":\"popup#ok_btn\"")
expect(found.2).to_contain("\"kind\":\"button\"")
val missing = handle_test_request(
    "/api/test/ui/observe",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(missing.0).to_equal(400)
expect(missing.2).to_contain("Missing selector")
```

</details>

#### queries structured canonical nodes and rejects missing canonical targets

1. session current state
   - Expected: found.0 equals `200`
   - Expected: found.1 equals `application/json`
2. session current state
   - Expected: missing.0 equals `404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val found = handle_test_request(
    "/api/test/ui/query?surface_id=popup&kind=button&text=OK&focused_only=false&limit=1",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(found.0).to_equal(200)
expect(found.1).to_equal("application/json")
expect(found.2).to_contain("\"match_count\":1")
expect(found.2).to_contain("\"canonical_id\":\"popup#ok_btn\"")
val missing = handle_test_request(
    "/api/test/ui/query?canonical_id=popup#missing",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(missing.0).to_equal(404)
expect(missing.2).to_contain("Canonical node not found")
```

</details>

#### ensures bounded declarative expectations over canonical queries

1. session current state
   - Expected: missing.0 equals `200`
2. session current state
   - Expected: focus.0 equals `200`
3. session current state
   - Expected: ensured.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val missing = handle_test_request(
    "/api/test/ui/ensure?surface_id=popup&kind=button&text=Missing&expectation=absent",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(missing.0).to_equal(200)
expect(missing.2).to_contain("\"satisfied\":true")
val focus = handle_test_request(
    "/api/test/ui/state",
    "POST",
    "{\"surface_id\":\"popup\",\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"focused\",\"state_value\":\"true\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(focus.0).to_equal(200)
val ensured = handle_test_request(
    "/api/test/ui/ensure?surface_id=popup&kind=button&focused_only=true&expectation=match_count&expected_value=1&limit=1",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(ensured.0).to_equal(200)
expect(ensured.2).to_contain("\"satisfied\":true")
expect(ensured.2).to_contain("\"match_count\":1")
expect(ensured.2).to_contain("\"canonical_id\":\"popup#ok_btn\"")
```

</details>

#### preserves focused semantics across state, observe, and query

1. session current state
   - Expected: empty.0 equals `200`
2. session current state
   - Expected: focus.0 equals `200`
3. session current state
   - Expected: observed.0 equals `200`
4. session current state
   - Expected: query.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val empty = handle_test_request(
    "/api/test/ui/query?surface_id=popup&kind=button&focused_only=true&limit=1",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(empty.0).to_equal(200)
expect(empty.2).to_contain("\"match_count\":0")
val focus = handle_test_request(
    "/api/test/ui/state",
    "POST",
    "{\"surface_id\":\"popup\",\"canonical_id\":\"popup#ok_btn\",\"state_key\":\"focused\",\"state_value\":\"true\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(focus.0).to_equal(200)
expect(focus.2).to_contain("\"ok\":true")
val observed = handle_test_request(
    "/api/test/ui/observe?canonical_id=popup#ok_btn",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(observed.0).to_equal(200)
expect(observed.2).to_contain("\"canonical_id\":\"popup#ok_btn\"")
expect(observed.2).to_contain("\"focused\":true")
val query = handle_test_request(
    "/api/test/ui/query?surface_id=popup&kind=button&focused_only=true&limit=1",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(query.0).to_equal(200)
expect(query.2).to_contain("\"match_count\":1")
expect(query.2).to_contain("\"canonical_id\":\"popup#ok_btn\"")
```

</details>

#### reads and sets declarative UI state

1. session current state
   - Expected: read.0 equals `200`
2. session current state
   - Expected: read_key.0 equals `200`
3. session current state
   - Expected: surface_read.0 equals `200`
4. session current state
   - Expected: write.0 equals `200`
5. session current state
   - Expected: selected_false.0 equals `200`
6. session current state
   - Expected: missing.0 equals `400`
7. session current state
   - Expected: unsupported_key.0 equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 75 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val read = handle_test_request(
    "/api/test/ui/state?canonical_id=popup#ok_btn",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(read.0).to_equal(200)
expect(read.2).to_contain("\"canonical_id\":\"popup#ok_btn\"")
val read_key = handle_test_request(
    "/api/test/ui/state?canonical_id=popup#ok_btn&state_key=focused",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(read_key.0).to_equal(200)
expect(read_key.2).to_contain("\"state_key\":\"focused\"")
expect(read_key.2).to_contain("\"state_value\":\"false\"")
val surface_read = handle_test_request(
    "/api/test/ui/state?surface_id=popup&state_key=active",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(surface_read.0).to_equal(200)
expect(surface_read.2).to_contain("\"surface_id\":\"popup\"")
expect(surface_read.2).to_contain("\"state_value\":\"true\"")
val write = handle_test_request(
    "/api/test/ui/state",
    "POST",
    "{\"surface_id\":\"main\",\"canonical_id\":\"main#submit_btn\",\"state_key\":\"invoke\",\"state_value\":\"true\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(write.0).to_equal(200)
expect(write.2).to_contain("\"ok\":true")
expect(write.2).to_contain("click_submit_btn")
val selected_false = handle_test_request(
    "/api/test/ui/state",
    "POST",
    "{\"surface_id\":\"main\",\"canonical_id\":\"main#submit_btn\",\"state_key\":\"selected\",\"state_value\":\"false\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(selected_false.0).to_equal(200)
expect(selected_false.2).to_contain("\"state_key\":\"selected\"")
expect(selected_false.2).to_contain("\"state_value\":\"false\"")
val missing = handle_test_request(
    "/api/test/ui/state",
    "POST",
    "{\"state_value\":\"true\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(missing.0).to_equal(400)
expect(missing.2).to_contain("Missing required field: state_key")
val unsupported_key = handle_test_request(
    "/api/test/ui/state?canonical_id=popup#ok_btn&state_key=bogus",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(unsupported_key.0).to_equal(400)
expect(unsupported_key.2).to_contain("Unsupported state key")
```

</details>

#### reads and writes typed values for value-bearing nodes

1. session current state
   - Expected: read.0 equals `200`
2. session current state
   - Expected: write.0 equals `200`
3. session current state
   - Expected: unsupported.0 equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val read = handle_test_request(
    "/api/test/ui/value?canonical_id=main#name_input",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(read.0).to_equal(200)
expect(read.2).to_contain("\"canonical_id\":\"main#name_input\"")
expect(read.2).to_contain("\"value\":\"Ada\"")
val write = handle_test_request(
    "/api/test/ui/value",
    "POST",
    "{\"surface_id\":\"main\",\"canonical_id\":\"main#name_input\",\"value\":\"Grace\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(write.0).to_equal(200)
expect(write.2).to_contain("\"value\":\"Grace\"")
val unsupported = handle_test_request(
    "/api/test/ui/value?canonical_id=main#submit_btn",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(unsupported.0).to_equal(400)
expect(unsupported.2).to_contain("Unsupported value target")
```

</details>

#### serves additive adapter snapshots and visual probes

1. session current state
   - Expected: adapter.0 equals `200`
2. session current state
   - Expected: probe.0 equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val adapter = handle_test_request(
    "/api/test/ui/adapter_snapshot?surface_id=popup",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(adapter.0).to_equal(200)
expect(adapter.2).to_contain("\"source_kind\":\"session\"")
expect(adapter.2).to_contain("\"surface_id\":\"popup\"")
expect(adapter.2).to_contain("\"issues\":[]")
val probe = handle_test_request(
    "/api/test/ui/visual_probe?surface_id=popup",
    "GET",
    "",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(probe.0).to_equal(200)
expect(probe.2).to_contain("\"active_surface\":\"popup\"")
expect(probe.2).to_contain("\"captured\":false")
expect(probe.2).to_contain("\"mark_id\":\"mark_1\"")
```

</details>

#### accepts canonical actions, switches surface, and rejects empty or missing targets

1. session current state
   - Expected: ok.0 equals `200`
   - Expected: session.active_surface() equals `popup`
2. session current state
   - Expected: semantic.0 equals `200`
   - Expected: session.active_surface() equals `main`
3. session current state
   - Expected: missing_target.0 equals `400`
4. session current state
   - Expected: invalid_surface.0 equals `404`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _session_with_popup()
val ok = handle_test_request(
    "/api/test/ui/act",
    "POST",
    "{\"surface_id\":\"popup\",\"canonical_id\":\"popup#ok_btn\",\"action\":\"click\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(ok.0).to_equal(200)
expect(ok.2).to_contain("\"surface_id\":\"popup\"")
expect(ok.2).to_contain("\"canonical_id\":\"popup#ok_btn\"")
expect(session.active_surface()).to_equal("popup")
val semantic = handle_test_request(
    "/api/test/ui/act",
    "POST",
    "{\"surface_id\":\"main\",\"canonical_id\":\"main#submit_btn\",\"action\":\"submit\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(semantic.0).to_equal(200)
expect(semantic.2).to_contain("\"surface_id\":\"main\"")
expect(session.active_surface()).to_equal("main")
val missing_target = handle_test_request(
    "/api/test/ui/act",
    "POST",
    "{\"action\":\"click\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(missing_target.0).to_equal(400)
expect(missing_target.2).to_contain("Missing required field: surface_id")
val invalid_surface = handle_test_request(
    "/api/test/ui/act",
    "POST",
    "{\"surface_id\":\"missing\",\"action\":\"click\"}",
    session.current_state(),
    \_: pass_dn,
    session
)
expect(invalid_surface.0).to_equal(404)
expect(invalid_surface.2).to_contain("Surface not found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ui_access_http_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui_access_protocol HTTP routes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
