# Ui Access Protocol Specification

> Tests covering ui_access_protocol feature spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Protocol Specification

## Scenarios

### ui_access_protocol feature spec

#### REQ-UAP-001 and REQ-UAP-004 expose a canonical multi-surface snapshot

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-UAP-001 and REQ-UAP-004 expose a canonical multi-surface snapshot
   - Expected: snapshot.protocol_version equals `1`
   - Expected: snapshot.surfaces.len() equals `2`
   - Expected: snapshot.active_surface equals `popup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-001 and REQ-UAP-004 expose a canonical multi-surface snapshot")
val session = _session_with_popup()
val snapshot = session.access_snapshot()
expect(snapshot.protocol_version).to_equal(1)
expect(snapshot.surfaces.len()).to_equal(2)
expect(snapshot.active_surface).to_equal("popup")
```

</details>

#### REQ-UAP-002 uses readable canonical node ids

- REQ-UAP-002 uses readable canonical node ids
   - Expected: ui_access_canonical_id("popup", "ok_btn") equals `popup#ok_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-002 uses readable canonical node ids")
expect(ui_access_canonical_id("popup", "ok_btn")).to_equal("popup#ok_btn")
```

</details>

#### REQ-UAP-007 and REQ-UAP-008 record recent surface-scoped history

- REQ-UAP-007 and REQ-UAP-008 record recent surface-scoped history
   - Expected: popup_events[0].surface_id equals `popup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-007 and REQ-UAP-008 record recent surface-scoped history")
val session = _session_with_popup()
session.dispatch(UIEvent.Action(name: "ok"))
val popup_events = session.access_recent_surface_events("popup", 10)
expect(popup_events.len()).to_be_greater_than(0)
expect(popup_events[0].surface_id).to_equal("popup")
```

</details>

#### REQ-UAP-018 persists history and searchable nodes when a store is attached

- REQ-UAP-018 persists history and searchable nodes when a store is attached
   - Expected: persisted_events[0].surface_id equals `popup`
   - Expected: persisted_nodes.len() equals `1`
   - Expected: persisted_nodes[0].canonical_id equals `popup#ok_btn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-018 persists history and searchable nodes when a store is attached")
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

- REQ-UAP-019 enriches live surfaces with registry window metadata without persisting runtime handles
   - Expected: snapshot.surfaces.len() equals `2`
   - Expected: popup_window_id equals `55`
   - Expected: popup_app_id equals `app.popup`
   - Expected: persisted_window_id equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-019 enriches live surfaces with registry window metadata without persisting runtime handles")
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

- REQ-UAP-010 and REQ-UAP-013 expose declarative observe/state/query/ensure helpers over canonical ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-010 and REQ-UAP-013 expose declarative observe/state/query/ensure helpers over canonical ids")
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

- REQ-UAP-020 and REQ-UAP-021 expose typed value reads and writes only for input, textfield, and textarea nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-020 and REQ-UAP-021 expose typed value reads and writes only for input, textfield, and textarea nodes")
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

- REQ-UAP-022 and REQ-UAP-023 expose additive adapter envelopes and semantic vision probes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-UAP-022 and REQ-UAP-023 expose additive adapter envelopes and semantic vision probes")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ui_access_protocol feature spec.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-UAP-004`
- `REQ-UAP-008`
- `REQ-UAP-013`
- `REQ-UAP-021`
- `REQ-UAP-023`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `00356d3d613cdf4328caa0352720fce840ff55a5ca4ce1aaf041a51e5cdb60e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00356d3d613cdf4328caa0352720fce840ff55a5ca4ce1aaf041a51e5cdb60e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00356d3d613cdf4328caa0352720fce840ff55a5ca4ce1aaf041a51e5cdb60e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/os/feature/ui_access_protocol_spec.spl
mirror: doc/06_spec/03_system/app/os/feature/ui_access_protocol_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/os/feature/ui_access_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/os/feature/ui_access_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/os/feature/ui_access_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/os/feature/ui_access_protocol_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-UAP-001 and REQ-UAP-004 expose a canonical multi-surface snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/ui_access_protocol_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-UAP-002 uses readable canonical node ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/ui_access_protocol_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-UAP-007 and REQ-UAP-008 record recent surface-scoped history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
