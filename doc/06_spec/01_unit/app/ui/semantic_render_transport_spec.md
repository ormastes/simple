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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Render Transport Specification

## Scenarios

### semantic render transport bridge

#### attaches semantic snapshots at the shared render IPC boundary

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
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
```

</details>

#### exposes backend semantic snapshot envelopes through one target-aware shape

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val electron = ElectronBackend.new(4021).unwrap()

val electron_json = electron.semantic_snapshot_json(state)
expect(electron_json.len()).to_be_greater_than(0)
expect(electron_json).to_contain("stage")
expect(electron.semantic_snapshot_envelope_json(state, "main", 10u64)).to_contain("snapshot")
val snapshot_env = WebRenderSnapshotEnvelope(target: WEB_RENDER_TARGET_ELECTRON, surface_id: "main", revision: 10u64, snapshot_json: "{\"ok\":true}")
val snapshot_json = web_render_snapshot_envelope_to_json_with_semantic(snapshot_env, electron_json)
expect(snapshot_json).to_contain("\"semantic\":{\"protocol_version\"")
val command = SemanticUiCommand.type_text("main", "web_render_action", "Run")
val bundle = semantic_ui_render_transport_bundle(WEB_RENDER_TARGET_ELECTRON, "main", electron_semantic_snapshot(state), command, 10u64, 10u64, 11u64, "[]")
expect(bundle.input_json).to_contain("event_type")
expect(bundle.input_json).to_contain("web_render_action")
expect(bundle.snapshot_json).to_contain("snapshot")
expect(bundle.patch_json).to_contain("patches")
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
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
