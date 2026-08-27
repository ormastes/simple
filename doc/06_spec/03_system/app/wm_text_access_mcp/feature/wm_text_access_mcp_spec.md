# wm_text_access_mcp_spec

> WM Text Access MCP source contract spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_text_access_mcp_spec

WM Text Access MCP source contract spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

WM Text Access MCP source contract spec.
Verifies that the selected common window-to-text module and adapter entrypoints exist and are wired through the UI access hub.

## Scenarios

### WM text access MCP

#### REQ-WTA-001 defines the common window-to-text model

- REQ-WTA-001 defines the common window-to-text model


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-001 defines the common window-to-text model")
val src = _src()
expect(src).to_contain("struct WinTextSource")
expect(src).to_contain("struct WinTextSnapshot")
expect(src).to_contain("struct WinTextActionRequest")
expect(src).to_contain("struct WinTextActionResult")
```

</details>

#### REQ-WTA-002 implements shared query logic over normalized snapshots

- REQ-WTA-002 implements shared query logic over normalized snapshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-002 implements shared query logic over normalized snapshots")
val src = _src()
expect(src).to_contain("fn win_text_find_nodes")
expect(src).to_contain("ui_access_find_nodes(snapshot.access")
```

</details>

#### REQ-WTA-003 implements shared action routing and unsupported results

- REQ-WTA-003 implements shared action routing and unsupported results


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-003 implements shared action routing and unsupported results")
val src = _src()
expect(src).to_contain("fn win_text_route_action")
expect(src).to_contain("WIN_TEXT_ACTION_UNSUPPORTED")
expect(src).to_contain("win_text_node_supports_action")
```

</details>

#### REQ-WTA-004 includes TRACE32 text window adapter support

- REQ-WTA-004 includes TRACE32 text window adapter support


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-004 includes TRACE32 text window adapter support")
val src = _src()
expect(src).to_contain("fn win_text_trace32_snapshot")
expect(src).to_contain("WIN_TEXT_SOURCE_TRACE32")
expect(src).to_contain("open_command")
expect(src).to_contain("capture_command")
expect(src).to_contain("captured_text.split")
```

</details>

#### REQ-WTA-005 includes Simple UI adapter support

- REQ-WTA-005 includes Simple UI adapter support


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-005 includes Simple UI adapter support")
val src = _src()
expect(src).to_contain("fn win_text_simple_ui_snapshot")
expect(src).to_contain("WIN_TEXT_SOURCE_SIMPLE_UI")
expect(src).to_contain("in_process_semantic")
```

</details>

#### REQ-WTA-006 includes host WM top-level adapter support

- REQ-WTA-006 includes host WM top-level adapter support


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-006 includes host WM top-level adapter support")
val src = _src()
expect(src).to_contain("fn win_text_host_wm_single_window_snapshot")
expect(src.contains("play.types.{WindowInfo}")).to_be(false)
expect(src).to_contain("WIN_TEXT_SOURCE_HOST_WM")
expect(src).to_contain("host_window")
expect(src).to_contain("click_xy")
```

</details>

#### REQ-WTA-007 exposes the common module through the UI access hub

- REQ-WTA-007 exposes the common module through the UI access hub


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-007 exposes the common module through the UI access hub")
val hub = _hub()
expect(hub).to_contain("use common.ui.win_text_access")
expect(hub).to_contain("win_text_trace32_snapshot")
expect(hub).to_contain("win_text_host_wm_single_window_snapshot")
expect(hub).to_contain("win_text_route_action")
```

</details>

#### REQ-WTA-007 exposes an MCP status hook for the common access surface

- REQ-WTA-007 exposes an MCP status hook for the common access surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-007 exposes an MCP status hook for the common access surface")
val tools = _mcp_tools()
val dispatch = _mcp_dispatch()
val play = _mcp_play()
val static_tools = _mcp_static()
expect(tools).to_contain("play_wm_text_status")
expect(static_tools).to_contain("play_wm_text_status")
expect(dispatch).to_contain("handle_play_wm_text_status")
expect(play).to_contain("common.ui.win_text_access")
expect(play).to_contain("trace32")
expect(play).to_contain("simple_ui")
expect(play).to_contain("host_wm")
```

</details>

#### REQ-WTA-007 exposes live MCP facade tools for snapshot, find, and act

- REQ-WTA-007 exposes live MCP facade tools for snapshot, find, and act


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-007 exposes live MCP facade tools for snapshot, find, and act")
val tools = _mcp_tools()
val dispatch = _mcp_dispatch()
val play = _mcp_play()
val static_tools = _mcp_static()
expect(tools).to_contain("play_wm_text_snapshot")
expect(tools).to_contain("play_wm_text_find")
expect(tools).to_contain("play_wm_text_act")
expect(static_tools).to_contain("play_wm_text_snapshot")
expect(static_tools).to_contain("play_wm_text_find")
expect(static_tools).to_contain("play_wm_text_act")
expect(dispatch).to_contain("handle_play_wm_text_snapshot")
expect(dispatch).to_contain("handle_play_wm_text_find")
expect(dispatch).to_contain("handle_play_wm_text_act")
expect(play).to_contain("fn handle_play_wm_text_snapshot")
expect(play).to_contain("fn handle_play_wm_text_find")
expect(play).to_contain("fn handle_play_wm_text_act")
```

</details>

#### REQ-WTA-007 MCP facade uses shared win_text core instead of backend-specific query duplication

- REQ-WTA-007 MCP facade uses shared win_text core instead of backend-specific query duplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-007 MCP facade uses shared win_text core instead of backend-specific query duplication")
val play = _mcp_play()
expect(play).to_contain("win_text_trace32_snapshot")
expect(play).to_contain("win_text_simple_ui_snapshot")
expect(play).to_contain("win_text_host_wm_single_window_snapshot")
expect(play).to_contain("win_text_find_nodes")
expect(play).to_contain("win_text_route_action")
```

</details>

#### REQ-WTA-007 exposes CLI planner names for the common WM text facade

- REQ-WTA-007 exposes CLI planner names for the common WM text facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-007 exposes CLI planner names for the common WM text facade")
val cli = _play_cli()
expect(cli).to_contain("wm-text-snapshot")
expect(cli).to_contain("wm-text-find")
expect(cli).to_contain("wm-text-act")
expect(cli).to_contain("args[0] == \"play\"")
```

</details>

#### REQ-WTA-007 keeps the native CLI driver registered for simple play

- REQ-WTA-007 keeps the native CLI driver registered for simple play


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("REQ-WTA-007 keeps the native CLI driver registered for simple play")
val driver = _rust_driver()
expect(driver).to_contain("name: \"play\"")
expect(driver).to_contain("app_path: \"src/app/play/main.spl\"")
expect(driver).to_contain("error: play app not found")
expect(driver).to_contain("app_relative_path == \"src/app/play/main.spl\"")
expect(driver).to_contain("SIMPLE_FORCE_ARGS")
```

</details>

#### NFR-WTA-002 exposes staleness metadata and calculation

- NFR-WTA-002 exposes staleness metadata and calculation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NFR-WTA-002 exposes staleness metadata and calculation")
val src = _src()
expect(src).to_contain("captured_at_ms")
expect(src).to_contain("max_age_ms")
expect(src).to_contain("stale: bool")
expect(src).to_contain("fn win_text_is_stale")
```

</details>

#### NFR-WTA-003 keeps query hot paths in memory

- NFR-WTA-003 keeps query hot paths in memory
   - Expected: src does not contain `rt_process_run`
   - Expected: src does not contain `wm_list_windows(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("NFR-WTA-003 keeps query hot paths in memory")
val src = _src()
expect(src).to_contain("fn win_text_find_nodes")
expect(src.contains("rt_process_run")).to_equal(false)
expect(src.contains("wm_list_windows(")).to_equal(false)
```

</details>

#### AC-WTA-01 wraps TRACE32 captured text into queryable nodes

- AC-WTA-01 wraps TRACE32 captured text into queryable nodes
   - Expected: snapshot.access.surfaces.len() equals `1`
   - Expected: matches.len() equals `1`
   - Expected: matches[0].surface_id equals `trace32:Data.List`
   - Expected: snapshot.sources[0].stale is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-WTA-01 wraps TRACE32 captured text into queryable nodes")
val snapshot = win_text_trace32_snapshot(window_key: "Data.List", title: "TRACE32 Data.List", open_command: "WinPOS Data.List", capture_command: "PRinTer.FILE", capture_mode: "printer", captured_text: "PC=0x1000\nR0=1", captured_at_ms: 100, max_age_ms: 1000, now_ms: 200)
val matches = win_text_find_nodes(snapshot, "", "text", "PC=0x1000", 10)
expect(snapshot.access.surfaces.len()).to_equal(1)
expect(matches.len()).to_equal(1)
expect(matches[0].surface_id).to_equal("trace32:Data.List")
expect(snapshot.sources[0].stale).to_equal(false)
```

</details>

#### AC-WTA-02 wraps Simple UI snapshots while preserving IDs

- AC-WTA-02 wraps Simple UI snapshots while preserving IDs
   - Expected: snapshot.access.snapshot_revision equals `7`
   - Expected: matches.len() equals `1`
   - Expected: matches[0].canonical_id equals `simple:main#run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-WTA-02 wraps Simple UI snapshots while preserving IDs")
val surface = UiAccessSurface(surface_id: "simple:main", title: "Simple App", active: true, window_id: "main", app_id: "simple", root_canonical_id: ui_access_canonical_id("simple:main", "root"))
val node = win_text_make_node(surface_id: "simple:main", widget_id: "run", kind: "button", text_value: "Run", action_names: ["click"], props: [UiAccessProp(key: "source", value: "simple_ui")])
val access = UiAccessSnapshot(protocol_version: 1, snapshot_revision: 7, mode: "simple_ui", active_surface: "simple:main", surfaces: [surface], nodes: [node], recent_events: [])
val snapshot = win_text_simple_ui_snapshot(access, 100, 1000, 200)
val matches = win_text_find_nodes(snapshot, "simple:main", "button", "Run", 10)
expect(snapshot.access.snapshot_revision).to_equal(7)
expect(matches.len()).to_equal(1)
expect(matches[0].canonical_id).to_equal("simple:main#run")
```

</details>

#### AC-WTA-03 wraps host WM windows with top-level capabilities only

- AC-WTA-03 wraps host WM windows with top-level capabilities only
   - Expected: snapshot.access.surfaces.len() equals `1`
   - Expected: matches.len() equals `1`
   - Expected: matches[0].action_names contains `focus`
   - Expected: matches[0].action_names does not contain `set_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-WTA-03 wraps host WM windows with top-level capabilities only")
val snapshot = win_text_host_wm_single_window_snapshot(window_id: "42", target_id: "target-42", title: "TRACE32 MDI", url: "", x: 0, y: 0, width: 1024, height: 768, focused: true, captured_at_ms: 100, max_age_ms: 1000, now_ms: 200)
val matches = win_text_find_nodes(snapshot, "", "host_window", "TRACE32", 10)
expect(snapshot.access.surfaces.len()).to_equal(1)
expect(matches.len()).to_equal(1)
expect(matches[0].action_names.contains("focus")).to_equal(true)
expect(matches[0].action_names.contains("set_value")).to_equal(false)
```

</details>

#### AC-WTA-04 queries merged TRACE32, Simple UI, and host WM snapshots

- AC-WTA-04 queries merged TRACE32, Simple UI, and host WM snapshots
   - Expected: win_text_find_nodes(merged, "", "text", "A0=5", 10).len() equals `1`
   - Expected: win_text_find_nodes(merged, "", "label", "Ready", 10).len() equals `1`
   - Expected: win_text_find_nodes(merged, "", "host_window", "TRACE32", 10).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-WTA-04 queries merged TRACE32, Simple UI, and host WM snapshots")
val t32 = win_text_trace32_snapshot(window_key: "Register", title: "Registers", open_command: "WinPOS Register", capture_command: "PRinTer.FILE", capture_mode: "printer", captured_text: "A0=5", captured_at_ms: 100, max_age_ms: 1000, now_ms: 200)
val simple_surface = UiAccessSurface(surface_id: "simple:main", title: "Simple App", active: true, window_id: "main", app_id: "simple", root_canonical_id: ui_access_canonical_id("simple:main", "root"))
val simple_node = win_text_make_node(surface_id: "simple:main", widget_id: "status", kind: "label", text_value: "Ready", action_names: [], props: [UiAccessProp(key: "source", value: "simple_ui")])
val simple = win_text_simple_ui_snapshot(UiAccessSnapshot(protocol_version: 1, snapshot_revision: 1, mode: "simple_ui", active_surface: "simple:main", surfaces: [simple_surface], nodes: [simple_node], recent_events: []), 100, 1000, 200)
val wm = win_text_host_wm_single_window_snapshot(window_id: "42", target_id: "target-42", title: "TRACE32 MDI", url: "", x: 0, y: 0, width: 1024, height: 768, focused: true, captured_at_ms: 100, max_age_ms: 1000, now_ms: 200)
val merged = win_text_merge_snapshots("merged", [t32, simple, wm])
expect(win_text_find_nodes(merged, "", "text", "A0=5", 10).len()).to_equal(1)
expect(win_text_find_nodes(merged, "", "label", "Ready", 10).len()).to_equal(1)
expect(win_text_find_nodes(merged, "", "host_window", "TRACE32", 10).len()).to_equal(1)
```

</details>

#### AC-WTA-05 and AC-WTA-06 route supported actions and reject unsupported actions

- AC-WTA-05 and AC-WTA-06 route supported actions and reject unsupported actions
   - Expected: supported.ok is true
   - Expected: supported.source_id equals `host_wm`
   - Expected: unsupported.ok is false
   - Expected: unsupported.code equals `unsupported_operation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-WTA-05 and AC-WTA-06 route supported actions and reject unsupported actions")
val snapshot = win_text_host_wm_single_window_snapshot(window_id: "42", target_id: "target-42", title: "TRACE32 MDI", url: "", x: 0, y: 0, width: 1024, height: 768, focused: true, captured_at_ms: 100, max_age_ms: 1000, now_ms: 200)
val supported = win_text_route_action(snapshot, WinTextActionRequest(target_id: "wm:42#root", action: "focus", text_value: "", x: 0, y: 0))
val unsupported = win_text_route_action(snapshot, WinTextActionRequest(target_id: "wm:42#root", action: "set_value", text_value: "x", x: 0, y: 0))
expect(supported.ok).to_equal(true)
expect(supported.source_id).to_equal("host_wm")
expect(unsupported.ok).to_equal(false)
expect(unsupported.code).to_equal("unsupported_operation")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a0053e529a3e7928e8d1cb5ceb0ee1ac098cb070c851ef036f19543e6dbc9ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a0053e529a3e7928e8d1cb5ceb0ee1ac098cb070c851ef036f19543e6dbc9ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a0053e529a3e7928e8d1cb5ceb0ee1ac098cb070c851ef036f19543e6dbc9ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl
mirror: doc/06_spec/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-WTA-001 defines the common window-to-text model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-WTA-002 implements shared query logic over normalized snapshots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/wm_text_access_mcp/feature/wm_text_access_mcp_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-WTA-003 implements shared action routing and unsupported results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
