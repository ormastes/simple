# Semantic Backend Helpers Specification

## Scenarios

### semantic backend helpers

#### exposes shared semantic snapshots for web and staged host adapters

1.  expect common snapshot

2.  expect common snapshot


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = _semantic_backend_state()

val web = web_semantic_snapshot(state)
val tui = tui_semantic_snapshot(state)
val electron = electron_semantic_snapshot(state)
val tauri = tauri_semantic_snapshot(state)
val none = none_semantic_snapshot(state)

expect(web.stage).to_equal(SEMANTIC_UI_STAGE_PROTOCOL)
expect(tui.stage).to_equal(SEMANTIC_UI_STAGE_STATE)
expect(electron.stage).to_equal(SEMANTIC_UI_STAGE_RENDERER)
expect(tauri.stage).to_equal(SEMANTIC_UI_STAGE_RENDERER)
expect(none.stage).to_equal(SEMANTIC_UI_STAGE_STATE)

expect(web.elements.len()).to_equal(tui.elements.len())
expect(web.elements.len()).to_equal(electron.elements.len())
expect(web.elements.len()).to_equal(tauri.elements.len())
expect(web.elements.len()).to_equal(none.elements.len())
expect(web.elements[0].canonical_id).to_equal(tui.elements[0].canonical_id)
expect(web.elements[0].canonical_id).to_equal(electron.elements[0].canonical_id)

_expect_common_snapshot(web.stage, web.state.title, web.state.element_count, web.state.focused_id)
_expect_common_snapshot(tui.stage, tui.state.title, tui.state.element_count, tui.state.focused_id)
```

</details>

#### orders helper stages by maturity

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = _semantic_backend_state()
val web = web_semantic_snapshot(state)
val electron = electron_semantic_snapshot(state)
val tui = tui_semantic_snapshot(state)

expect(semantic_ui_stage_at_least(web.stage, SEMANTIC_UI_STAGE_RENDERER)).to_equal(true)
expect(semantic_ui_stage_at_least(electron.stage, SEMANTIC_UI_STAGE_STATE)).to_equal(true)
expect(semantic_ui_stage_at_least(tui.stage, SEMANTIC_UI_STAGE_RENDERER)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/semantic_backend_helpers_spec.spl` |
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

