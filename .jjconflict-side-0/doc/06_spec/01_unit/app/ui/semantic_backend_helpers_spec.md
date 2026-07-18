# Semantic Backend Helpers Specification

> 1.  expect common snapshot

<!-- sdn-diagram:id=semantic_backend_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semantic_backend_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semantic_backend_helpers_spec -> std
semantic_backend_helpers_spec -> common
semantic_backend_helpers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semantic_backend_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Backend Helpers Specification

## Scenarios

### semantic backend helpers

#### exposes shared semantic snapshots for web and staged host adapters

1.  expect common snapshot

2.  expect common snapshot

3.  expect common snapshot


<details>
<summary>Executable SPipe</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = _semantic_backend_state()

val web = web_semantic_snapshot(state)
val tui = tui_semantic_snapshot(state)
val tui_web = tui_web_semantic_snapshot(state)
val electron = electron_semantic_snapshot(state)
val tauri = tauri_semantic_snapshot(state)
val none = none_semantic_snapshot(state)
val browser = browser_semantic_snapshot(state)

expect(web.stage).to_equal(SEMANTIC_UI_STAGE_PROTOCOL)
expect(tui.stage).to_equal(SEMANTIC_UI_STAGE_STATE)
expect(tui_web.stage).to_equal(SEMANTIC_UI_STAGE_PROTOCOL)
expect(electron.stage).to_equal(SEMANTIC_UI_STAGE_RENDERER)
expect(tauri.stage).to_equal(SEMANTIC_UI_STAGE_RENDERER)
expect(none.stage).to_equal(SEMANTIC_UI_STAGE_STATE)
expect(browser.stage).to_equal(SEMANTIC_UI_STAGE_RENDERER)

expect(web.elements.len()).to_equal(tui.elements.len())
expect(web.elements.len()).to_equal(tui_web.elements.len())
expect(web.elements.len()).to_equal(electron.elements.len())
expect(web.elements.len()).to_equal(tauri.elements.len())
expect(web.elements.len()).to_equal(none.elements.len())
expect(web.elements.len()).to_equal(browser.elements.len())
expect(web.elements[0].canonical_id).to_equal(tui.elements[0].canonical_id)
expect(web.elements[0].canonical_id).to_equal(tui_web.elements[0].canonical_id)
expect(web.elements[0].canonical_id).to_equal(electron.elements[0].canonical_id)
expect(web.elements[0].canonical_id).to_equal(browser.elements[0].canonical_id)

expect(semantic_ui_has_capability(web, "Mouse")).to_equal(true)
expect(semantic_ui_has_capability(web, "Touch")).to_equal(true)
expect(semantic_ui_has_capability(electron, "Mouse")).to_equal(true)
expect(semantic_ui_has_capability(electron, "NativeDialogs")).to_equal(true)
expect(semantic_ui_has_capability(tauri, "Notification")).to_equal(true)
expect(semantic_ui_has_capability(tui, "Color")).to_equal(true)
expect(semantic_ui_has_capability(tui, "Images")).to_equal(false)
expect(semantic_ui_has_capability(tui_web, "Color")).to_equal(true)
expect(semantic_ui_has_capability(tui_web, "Mouse")).to_equal(false)
expect(semantic_ui_has_capability(browser, "Mouse")).to_equal(true)
expect(semantic_ui_has_capability(browser, "Images")).to_equal(true)
expect(semantic_ui_has_capability(browser, "Touch")).to_equal(true)
expect(none.capabilities.len()).to_equal(0)

_expect_common_snapshot(web.stage, web.state.title, web.state.element_count, web.state.focused_id)
_expect_common_snapshot(tui.stage, tui.state.title, tui.state.element_count, tui.state.focused_id)
_expect_common_snapshot(tui_web.stage, tui_web.state.title, tui_web.state.element_count, tui_web.state.focused_id)
```

</details>

#### orders helper stages by maturity

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = _semantic_backend_state()
val web = web_semantic_snapshot(state)
val electron = electron_semantic_snapshot(state)
val tui = tui_semantic_snapshot(state)
val browser = browser_semantic_snapshot(state)

expect(semantic_ui_stage_at_least(web.stage, SEMANTIC_UI_STAGE_RENDERER)).to_equal(true)
expect(semantic_ui_stage_at_least(electron.stage, SEMANTIC_UI_STAGE_STATE)).to_equal(true)
expect(semantic_ui_stage_at_least(browser.stage, SEMANTIC_UI_STAGE_STATE)).to_equal(true)
expect(semantic_ui_stage_at_least(tui.stage, SEMANTIC_UI_STAGE_RENDERER)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/semantic_backend_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- semantic backend helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
