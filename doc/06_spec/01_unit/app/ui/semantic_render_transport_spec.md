# Semantic Render Transport Specification

> <details>

<!-- sdn-diagram:id=semantic_render_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semantic_render_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semantic_render_transport_spec -> std
semantic_render_transport_spec -> common
semantic_render_transport_spec -> nogc_sync_mut
semantic_render_transport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semantic_render_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Render Transport Specification

## Scenarios

### semantic render transport bridge

#### attaches semantic snapshots at the shared render IPC boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val body = WebBackend.new(4020).render_html(state)
val req = WebRenderRequest.html(WEB_RENDER_TARGET_ELECTRON, "", body, "", "", 1280, 720)
val semantic_json = semantic_ui_snapshot_to_json(electron_semantic_snapshot(state))
val ipc = web_render_ipc_json_with_html_and_semantic(req, "<html><body><div id=\"app\">" + body + "</div></body></html>", semantic_json)

expect(ipc).to_contain("\"semantic\":{\"protocol_version\"")
expect(ipc).to_contain("\"stage\":\"S3\"")
expect(ipc).to_contain("\"element_count\":3")
expect(electron_semantic_render_ipc_json(state, 1280, 720)).to_contain("\"semantic\":{\"protocol_version\"")
expect(tauri_semantic_render_ipc_json(state, 1280, 720)).to_contain("\"target\":\"tauri\"")
expect(browser_semantic_render_ipc_json(state, 1280, 720)).to_contain("\"target\":\"pure_simple\"")
expect(browser_semantic_render_ipc_json(state, 1280, 720)).to_contain("\"semantic\":{\"protocol_version\"")
```

</details>

#### exposes backend semantic snapshot envelopes through one target-aware shape

<details>
<summary>Executable SPipe</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val web = WebBackend.new(4022)
val tui_web = TuiWebBackend.new()
val electron = ElectronBackend.new(4021).unwrap()
val tauri = TauriBackend.new(4023).unwrap()
val browser = BrowserBackend.create(640, 480, "software").unwrap()
val headless = NoneBackend.new().unwrap()

val electron_json = electron.semantic_snapshot_json(state)
expect(electron_json.len()).to_be_greater_than(0)
expect(electron_json).to_contain("stage")
expect(web.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"target\":\"simple_web\"")
expect(web.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"snapshot\"")
expect(tui_web.semantic_snapshot_json(state)).to_contain("\"stage\":\"S3\"")
expect(tui_web.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"target\":\"tui_web\"")
expect(tui_web.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"snapshot\"")
expect(electron.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("snapshot")
expect(tauri.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"target\":\"tauri\"")
expect(tauri.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"snapshot\"")
expect(browser.semantic_snapshot_json(state)).to_contain("\"stage\":\"S3\"")
expect(browser.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"target\":\"pure_simple\"")
expect(browser.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"snapshot\"")
expect(browser.semantic_render_ipc_json(state)).to_contain("\"semantic\":{\"protocol_version\"")
expect(headless.semantic_snapshot_json(state)).to_contain("\"stage\":\"S1\"")
expect(headless.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"target\":\"headless\"")
expect(headless.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("\"snapshot\"")
expect(tui_semantic_snapshot(state).stage).to_equal(SEMANTIC_UI_STAGE_STATE)
expect(none_semantic_snapshot(state).stage).to_equal(SEMANTIC_UI_STAGE_STATE)
val snapshot_env = WebRenderSnapshotEnvelope(target: WEB_RENDER_TARGET_ELECTRON, surface_id: "main", revision: 10u64, snapshot_json: "{\"ok\":true}")
val snapshot_json = web_render_snapshot_envelope_to_json_with_semantic(snapshot_env, electron_json)
expect(snapshot_json).to_contain("\"semantic\":{\"protocol_version\"")
val command = SemanticUiCommand.type_text("main", "web_render_action", "Run")
val bundle = semantic_ui_render_transport_bundle(WEB_RENDER_TARGET_ELECTRON, "main", electron_semantic_snapshot(state), command, 10u64, 10u64, 11u64, "[]")
val web_bundle = semantic_ui_render_transport_bundle(WEB_RENDER_TARGET_SIMPLE_WEB, "main", web_semantic_snapshot(state), command, 10u64, 10u64, 11u64, "[]")
val tui_web_bundle = semantic_ui_render_transport_bundle(WEB_RENDER_TARGET_TUI_WEB, "main", tui_web_semantic_snapshot(state), command, 10u64, 10u64, 11u64, "[]")
val tauri_bundle = semantic_ui_render_transport_bundle(WEB_RENDER_TARGET_TAURI, "main", tauri_semantic_snapshot(state), command, 10u64, 10u64, 11u64, "[]")
expect(bundle.input_json).to_contain("event_type")
expect(bundle.input_json).to_contain("web_render_action")
expect(bundle.snapshot_json).to_contain("snapshot")
expect(bundle.patch_json).to_contain("patches")
expect(web_bundle.snapshot_json).to_contain("\"target\":\"simple_web\"")
expect(tui_web_bundle.snapshot_json).to_contain("\"target\":\"tui_web\"")
expect(tauri_bundle.snapshot_json).to_contain("\"target\":\"tauri\"")
```

</details>

#### validates one semantic command transport shape across Web TUI Electron Tauri headless and pure Simple

<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val snapshot = web_semantic_snapshot(state)
val command = SemanticUiCommand.click("main", "web_render_action")
val matrix = semantic_ui_render_target_evidence_matrix(shared_render_targets(), "main", snapshot, command, 12u64, 12u64, 13u64, "[]")

expect(matrix.len()).to_equal(6)
for row in matrix:
    expect(row.surface_id).to_equal("main")
    expect(row.command_type).to_equal("click")
    expect(row.input_has_target).to_equal(true)
    expect(row.input_has_event).to_equal(true)
    expect(row.snapshot_has_target).to_equal(true)
    expect(row.snapshot_has_semantic).to_equal(true)
    expect(row.patch_has_target).to_equal(true)
    expect(row.patch_has_snapshot).to_equal(true)
    expect(row.ready).to_equal(true)
    expect(row.reason).to_equal("pass")
expect(matrix[0].target).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(matrix[1].target).to_equal(WEB_RENDER_TARGET_TUI_WEB)
expect(matrix[2].target).to_equal(WEB_RENDER_TARGET_ELECTRON)
expect(matrix[3].target).to_equal(WEB_RENDER_TARGET_TAURI)
expect(matrix[4].target).to_equal(WEB_RENDER_TARGET_HEADLESS)
expect(matrix[5].target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
expect(matrix[4].summary()).to_contain("target=headless")
expect(matrix[5].summary()).to_contain("target=pure_simple")
```

</details>

#### dispatches click type and focus commands through one session path across render targets

1. SemanticUiCommand click

2. SemanticUiCommand type text

3. SemanticUiCommand focus
   - Expected: matrix.len() equals `6`
   - Expected: row.command_type equals `command.command_type`
   - Expected: row.dispatch_ok is true
   - Expected: row.revision_advanced is true
   - Expected: row.recent_event_matches is true
   - Expected: row.read_after_write_observed is true
   - Expected: row.ready is true
   - Expected: row.reason equals `pass`
   - Expected: matrix[0].target equals `WEB_RENDER_TARGET_SIMPLE_WEB`
   - Expected: matrix[4].target equals `WEB_RENDER_TARGET_HEADLESS`
   - Expected: matrix[5].target equals `WEB_RENDER_TARGET_PURE_SIMPLE`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commands = [
    SemanticUiCommand.click("main", "web_render_action"),
    SemanticUiCommand.type_text("main", "web_render_action", "Run"),
    SemanticUiCommand.focus("main", "web_render_action")
]

for command in commands:
    val matrix = command_dispatch_matrix(command)
    expect(matrix.len()).to_equal(6)
    for row in matrix:
        expect(row.command_type).to_equal(command.command_type)
        expect(row.dispatch_ok).to_equal(true)
        expect(row.revision_advanced).to_equal(true)
        expect(row.recent_event_matches).to_equal(true)
        expect(row.read_after_write_observed).to_equal(true)
        expect(row.ready).to_equal(true)
        expect(row.reason).to_equal("pass")
    expect(matrix[0].target).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
    expect(matrix[4].target).to_equal(WEB_RENDER_TARGET_HEADLESS)
    expect(matrix[5].target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
    expect(matrix[5].summary()).to_contain("ready=true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/semantic_render_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- semantic render transport bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
