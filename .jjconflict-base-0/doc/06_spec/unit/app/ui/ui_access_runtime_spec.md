# Ui Access Runtime Specification

> Tests covering ui_access runtime attachment.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Runtime Specification

## Scenarios

### ui_access runtime attachment

#### builds a deterministic default runtime path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a deterministic default runtime path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a deterministic default runtime path")
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "")
val path = ui_access_store_runtime_path("examples/ui/hello_web.ui.sdn", "web")
expect(path).to_contain("ui_access")
expect(path).to_contain("web")
expect(path).to_end_with(".sqlite")
```

</details>

#### prefers explicit runtime config over the environment

- prefers explicit runtime config over the environment
   - Expected: path equals `/tmp/ui_access_config_override.sqlite`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers explicit runtime config over the environment")
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "/tmp/ui_access_env_override.sqlite")
val path = ui_access_store_runtime_path_with_override(
    "/tmp/ui_access_config_override.sqlite",
    "examples/ui/hello_web.ui.sdn",
    "web"
)
expect(path).to_equal("/tmp/ui_access_config_override.sqlite")
rt_env_set("SIMPLE_UI_ACCESS_DB_PATH", "")
```

</details>

#### auto-attaches a store for AsyncWebServer startup when runtime path is configured

- auto-attaches a store for AsyncWebServer startup when runtime path is configured
   - Expected: file_exists(db_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-attaches a store for AsyncWebServer startup when runtime path is configured")
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

- reuses persisted web history across server restarts with the same DB path
   - Expected: first_events[0].surface_id equals `main`
   - Expected: first_events[0].event_kind equals `action`
   - Expected: first_events[0].payload equals `submit`
   - Expected: restarted_events[0].surface_id equals `main`
   - Expected: restarted_events[0].event_kind equals `action`
   - Expected: restarted_events[0].payload equals `submit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses persisted web history across server restarts with the same DB path")
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

- auto-attaches a store for TuiWebServer startup when runtime path is configured
   - Expected: file_exists(db_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-attaches a store for TuiWebServer startup when runtime path is configured")
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

- auto-attaches a store for BrowserApp when an explicit runtime path is configured
   - Expected: events[0].surface_id equals `main`
   - Expected: events[0].event_kind equals `action`
   - Expected: file_exists(db_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-attaches a store for BrowserApp when an explicit runtime path is configured")
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
| Source | `test/unit/app/ui/ui_access_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui_access runtime attachment.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `83cfde8547f7019926dcbc7dac3da00d779db5a7260ca647b7a4fddbc2b9b2fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83cfde8547f7019926dcbc7dac3da00d779db5a7260ca647b7a4fddbc2b9b2fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83cfde8547f7019926dcbc7dac3da00d779db5a7260ca647b7a4fddbc2b9b2fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/ui_access_runtime_spec.spl
mirror: doc/06_spec/unit/app/ui/ui_access_runtime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/ui_access_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/ui_access_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/ui_access_runtime_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a deterministic default runtime path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ui_access_runtime_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers explicit runtime config over the environment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/ui_access_runtime_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'auto-attaches a store for AsyncWebServer startup when runtime path is configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
