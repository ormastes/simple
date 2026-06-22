# Ui Access Runtime Specification

> 1. rt env set

<!-- sdn-diagram:id=ui_access_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_runtime_spec -> std
ui_access_runtime_spec -> app
ui_access_runtime_spec -> common
ui_access_runtime_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Runtime Specification

## Scenarios

### ui_access runtime attachment

#### builds a deterministic default runtime path

1. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "")
val path = ui_access_store_runtime_path("examples/06_io/ui/hello_web.ui.sdn", "web")
expect(path).to_contain("ui_access")
expect(path).to_contain("web")
expect(path).to_end_with(".sqlite")
```

</details>

#### prefers explicit runtime config over the environment

1. rt env set
   - Expected: path equals `/tmp/ui_access_config_override.sqlite`
2. rt env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "/tmp/ui_access_env_override.sqlite")
val path = ui_access_store_runtime_path_with_override(
    "/tmp/ui_access_config_override.sqlite",
    "examples/06_io/ui/hello_web.ui.sdn",
    "web"
)
expect(path).to_equal("/tmp/ui_access_config_override.sqlite")
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "")
```

</details>

#### auto-attaches a store for AsyncWebServer startup when runtime path is configured

1. rt env set
2. file delete
   - Expected: file_exists(db_path) is true
3. rt env set
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/ui_access_async_web.sqlite"
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", db_path)
if file_exists(db_path):
    file_delete(db_path)
val server = AsyncWebServer.new("test/system/ui_browser/fixtures/hello.ui.sdn", 3011)?
val nodes = server.session.access_search_nodes("", "", "", 20)?
expect(nodes.len()).to_be_greater_than(0)
expect(file_exists(db_path)).to_equal(true)
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "")
if file_exists(db_path):
    file_delete(db_path)
```

</details>

#### reuses persisted web history across server restarts with the same DB path

1. file delete
2. first session dispatch
   - Expected: first_events[0].surface_id equals `main`
   - Expected: first_events[0].event_kind equals `action`
   - Expected: first_events[0].payload equals `submit`
   - Expected: restarted_events[0].surface_id equals `main`
   - Expected: restarted_events[0].event_kind equals `action`
   - Expected: restarted_events[0].payload equals `submit`
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/ui_access_async_web_restart.sqlite"
if file_exists(db_path):
    file_delete(db_path)
val first = AsyncWebServer.new_with_access_store_path(
    "test/system/ui_browser/fixtures/hello.ui.sdn",
    3013,
    db_path
)?
first.session.dispatch(UIEvent.Action(name: "submit"))
val first_events = first.session.access_persisted_events("main", 10)?
expect(first_events.len()).to_be_greater_than(0)
expect(first_events[0].surface_id).to_equal("main")
expect(first_events[0].event_kind).to_equal("action")
expect(first_events[0].payload).to_equal("submit")
val restarted = AsyncWebServer.new_with_access_store_path(
    "test/system/ui_browser/fixtures/hello.ui.sdn",
    3013,
    db_path
)?
val restarted_events = restarted.session.access_persisted_events("main", 10)?
expect(restarted_events.len()).to_be_greater_than(0)
expect(restarted_events[0].surface_id).to_equal("main")
expect(restarted_events[0].event_kind).to_equal("action")
expect(restarted_events[0].payload).to_equal("submit")
if file_exists(db_path):
    file_delete(db_path)
```

</details>

#### auto-attaches a store for TuiWebServer startup when runtime path is configured

1. rt env set
2. file delete
   - Expected: file_exists(db_path) is true
3. rt env set
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/ui_access_tui_web.sqlite"
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", db_path)
if file_exists(db_path):
    file_delete(db_path)
val server = TuiWebServer.new("test/system/ui_browser/fixtures/hello.ui.sdn", 3012)?
val nodes = server.session.access_search_nodes("", "", "", 20)?
expect(nodes.len()).to_be_greater_than(0)
expect(file_exists(db_path)).to_equal(true)
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "")
if file_exists(db_path):
    file_delete(db_path)
```

</details>

#### auto-attaches a store for BrowserApp when an explicit runtime path is configured

1. file delete
2. app session dispatch
   - Expected: events[0].surface_id equals `main`
   - Expected: events[0].event_kind equals `action`
   - Expected: file_exists(db_path) is true
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db_path = "/tmp/ui_access_browser.sqlite"
if file_exists(db_path):
    file_delete(db_path)
val app = BrowserApp.new_with_access_store_path(
    "test/system/ui_browser/fixtures/hello.ui.sdn",
    0,
    "software",
    db_path
)?
app.session.dispatch(UIEvent.Action(name: "submit"))
val events = app.session.access_persisted_events("main", 10)?
expect(events.len()).to_be_greater_than(0)
expect(events[0].surface_id).to_equal("main")
expect(events[0].event_kind).to_equal("action")
expect(file_exists(db_path)).to_equal(true)
if file_exists(db_path):
    file_delete(db_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ui_access_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui_access runtime attachment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
