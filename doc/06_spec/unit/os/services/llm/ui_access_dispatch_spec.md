# Ui Access Dispatch Specification

> Tests covering ui_access_protocol MCP dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Dispatch Specification

## Scenarios

### ui_access_protocol MCP dispatch

#### routes snapshot and surface reads through the canonical dispatcher

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes snapshot and surface reads through the canonical dispatcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes snapshot and surface reads through the canonical dispatcher")
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

- binds window metadata through the shared session registry


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds window metadata through the shared session registry")
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

- dispatches canonical actions and rejects invalid targets
   - Expected: bridge.session.active_surface() equals `popup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches canonical actions and rejects invalid targets")
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

- observes declarative state through snapshot, surface, node, and filtered reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("observes declarative state through snapshot, surface, node, and filtered reads")
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

- queries structured declarative results


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("queries structured declarative results")
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

- ensures bounded declarative expectations over canonical queries


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ensures bounded declarative expectations over canonical queries")
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

- preserves focused semantics across state, observe, and query


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves focused semantics across state, observe, and query")
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

- reads and sets declarative state through canonical targets
   - Expected: bridge.session.active_surface() equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads and sets declarative state through canonical targets")
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

- reads and writes typed values for value-bearing canonical nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads and writes typed values for value-bearing canonical nodes")
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

- reads additive adapter snapshots and vision probes


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads additive adapter snapshots and vision probes")
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

- rejects invalid declarative state transitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid declarative state transitions")
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

- reads persisted find and history results when a store is attached


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads persisted find and history results when a store is attached")
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

- auto-attaches a persisted store through CliGuiBridge.new when runtime path is configured


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-attaches a persisted store through CliGuiBridge.new when runtime path is configured")
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
| Source | `test/unit/os/services/llm/ui_access_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui_access_protocol MCP dispatch.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0275d09dacc766f80f8d579d55b6f450c7c4d75b9a13474a98a249efae47c3c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0275d09dacc766f80f8d579d55b6f450c7c4d75b9a13474a98a249efae47c3c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0275d09dacc766f80f8d579d55b6f450c7c4d75b9a13474a98a249efae47c3c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/services/llm/ui_access_dispatch_spec.spl
mirror: doc/06_spec/unit/os/services/llm/ui_access_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/services/llm/ui_access_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/llm/ui_access_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/llm/ui_access_dispatch_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes snapshot and surface reads through the canonical dispatcher' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/llm/ui_access_dispatch_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds window metadata through the shared session registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/llm/ui_access_dispatch_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches canonical actions and rejects invalid targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
