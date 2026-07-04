# Ui Layer Web Tauri Contract Specification

> 1. Err

<!-- sdn-diagram:id=ui_layer_web_tauri_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_layer_web_tauri_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_layer_web_tauri_contract_spec -> common
ui_layer_web_tauri_contract_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_layer_web_tauri_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Layer Web Tauri Contract Specification

## Scenarios

### 2D UI layer web and Tauri rendering contract

#### feeds Simple web and Tauri through the same artifact shape

1. Err
   - Expected: e equals ``

2. Ok
   - Expected: tauri.render_html(state) equals `body`
   - Expected: tauri.generate_full_page(state) equals `tauri_artifact.html`
   - Expected: tauri_render_ipc_json(state, tauri.viewport_width(), tauri.viewport_height()) equals `tauri_artifact.ipc_json`
   - Expected: tauri_artifact.target equals `WEB_RENDER_TARGET_TAURI`
   - Expected: tauri_artifact.capability_summary equals `web_render_capability_summary(WEB_RENDER_TARGET_TAURI)`
   - Expected: has_capability(tauri.capabilities(), Capability.Mouse) equals `has_capability(web_render_capabilities_for_target(WEB_RENDER_TARGET_TAURI), C... (full value in folded executable source)`
   - Expected: has_capability(tauri.capabilities(), Capability.Touch) equals `has_capability(web_render_capabilities_for_target(WEB_RENDER_TARGET_TAURI), C... (full value in folded executable source)`


<details>
<summary>Executable SPipe</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = contract_state()
val body = render_html_tree(state.tree.root_node(), state)

val web = WebBackend.new(4100)
expect(web.render_html(state)).to_equal(body)
val web_req = WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, "", body, "", "", web.viewport_width(), web.viewport_height())
val web_artifact = web_render_to_artifact(web_req)
expect(web.generate_full_page(state)).to_equal(web_artifact.html)
expect(web_artifact.target).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(web_artifact.html).to_contain("<div id=\"app\">")
expect(web_artifact.html).to_contain("widget-button")
expect(web_artifact.ipc_json).to_equal("")
expect(web_artifact.capability_summary).to_equal(web_render_capability_summary(WEB_RENDER_TARGET_SIMPLE_WEB))
expect(has_capability(web.capabilities(), Capability.Mouse)).to_equal(has_capability(web_render_capabilities_for_target(WEB_RENDER_TARGET_SIMPLE_WEB), Capability.Mouse))
expect(has_capability(web.capabilities(), Capability.Touch)).to_equal(has_capability(web_render_capabilities_for_target(WEB_RENDER_TARGET_SIMPLE_WEB), Capability.Touch))

val tauri_result = TauriBackend.new(4101)
match tauri_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tauri):
        expect(tauri.render_html(state)).to_equal(body)
        val tauri_req = WebRenderRequest.html(WEB_RENDER_TARGET_TAURI, "", body, generate_css(state.tree.theme_name()), "", tauri.viewport_width(), tauri.viewport_height())
        val tauri_artifact = web_render_to_artifact(tauri_req)
        expect(tauri.generate_full_page(state)).to_equal(tauri_artifact.html)
        expect(tauri_render_ipc_json(state, tauri.viewport_width(), tauri.viewport_height())).to_equal(tauri_artifact.ipc_json)
        expect(tauri_artifact.target).to_equal(WEB_RENDER_TARGET_TAURI)
        expect(tauri_artifact.html).to_contain("<div id=\"app\">")
        expect(tauri_artifact.html).to_contain("widget-button")
        expect(tauri_artifact.ipc_json).to_contain("\"target\":\"tauri\"")
        expect(tauri_artifact.capability_summary).to_equal(web_render_capability_summary(WEB_RENDER_TARGET_TAURI))
        expect(has_capability(tauri.capabilities(), Capability.Mouse)).to_equal(has_capability(web_render_capabilities_for_target(WEB_RENDER_TARGET_TAURI), Capability.Mouse))
        expect(has_capability(tauri.capabilities(), Capability.Touch)).to_equal(has_capability(web_render_capabilities_for_target(WEB_RENDER_TARGET_TAURI), Capability.Touch))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ui_layer_web_tauri_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- 2D UI layer web and Tauri rendering contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
