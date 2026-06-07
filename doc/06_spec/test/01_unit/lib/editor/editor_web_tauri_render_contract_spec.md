# Editor Web Tauri Render Contract Specification

> <details>

<!-- sdn-diagram:id=editor_web_tauri_render_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_web_tauri_render_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_web_tauri_render_contract_spec -> std
editor_web_tauri_render_contract_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_web_tauri_render_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Web Tauri Render Contract Specification

## Scenarios

### editor web and Tauri render contract

#### carries editor HTML through pure Simple WebRender artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = editor_render_contract_body()
val req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Simple IDE", body, "", "", 960, 640)
val artifact = web_render_to_artifact(req)
expect(artifact.target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
expect(artifact.html).to_contain("<div id=\"app\">")
expect(artifact.html).to_contain("gui-editor-source")
expect(artifact.html).to_contain("contenteditable=\"true\"")
expect(artifact.html).to_contain("data-language=\"markdown\"")
expect(artifact.ipc_json).to_equal("")
```

</details>

#### carries editor HTML through the Tauri render envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = editor_render_contract_body()
val req = WebRenderRequest.html(WEB_RENDER_TARGET_TAURI, "Simple IDE", body, ".gui-editor-source{font-family:monospace}", "", 960, 640).with_surface("main")
val artifact = web_render_to_artifact(req)
expect(artifact.target).to_equal(WEB_RENDER_TARGET_TAURI)
expect(artifact.html).to_contain("gui-editor-source")
expect(artifact.html).to_contain("contenteditable=\"true\"")
expect(artifact.ipc_json).to_contain("\"target\":\"tauri\"")
expect(artifact.ipc_json).to_contain("\"surface_id\":\"main\"")
expect(artifact.ipc_json).to_contain("gui-editor-source")
expect(artifact.ipc_json).to_contain("data-language=\\\"markdown\\\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/editor_web_tauri_render_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor web and Tauri render contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
