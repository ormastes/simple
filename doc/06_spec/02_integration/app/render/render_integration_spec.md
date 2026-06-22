# UI Render Integration Specification

> Integration tests for the render adapters. Validates that the dashboard adapter and office adapter produce meaningful output through the shared RenderResult contract, and that unknown adapter names are handled gracefully.

<!-- sdn-diagram:id=render_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=render_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

render_integration_spec -> std
render_integration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=render_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UI Render Integration Specification

Integration tests for the render adapters. Validates that the dashboard adapter and office adapter produce meaningful output through the shared RenderResult contract, and that unknown adapter names are handled gracefully.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UI-RENDER-002 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/05_design/ui_render_feature_caret.md |
| Research | N/A |
| Source | `test/02_integration/app/render/render_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Integration tests for the render adapters. Validates that the dashboard
adapter and office adapter produce meaningful output through the shared
RenderResult contract, and that unknown adapter names are handled gracefully.

## Key Concepts

| Concept | Description |
|---------|-------------|
| DashboardRenderRequest | Dashboard-specific render request with summary dict |
| render_dashboard | Dashboard adapter entry point producing RenderResult |
| office_render | Office adapter entry point routing to sub-apps |
| Adapter routing | Config.adapter_name selects which sub-app handles the request |

## Behavior

- Dashboard adapter produces text output containing status information
- Dashboard adapter produces HTML output containing styled cards
- Office adapter routes to word, sheets, slides, mail, planner, launcher
- Unknown adapter_name in office adapter returns warning message

## Scenarios

### Dashboard Render Adapter

#### text output for status mode

#### produces non-empty text output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_dashboard_config()
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
val len = result.text_output.len()
expect(len > 0).to_equal(true)
```

</details>

#### text output contains status header

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_dashboard_config()
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
expect(result.text_output).to_contain("Status")
```

</details>

#### text output contains feature count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_dashboard_config()
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
expect(result.text_output).to_contain("10")
```

</details>

#### sets metadata adapter to dashboard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_dashboard_config()
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
expect(result.metadata["adapter"]).to_equal("dashboard")
```

</details>

#### html output

#### produces non-empty html output when format is html

1. var cfg = default dashboard config
   - Expected: len > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = default_dashboard_config()
cfg.format = "html"
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
val len = result.html_output.len()
expect(len > 0).to_equal(true)
```

</details>

#### html output contains DOCTYPE

1. var cfg = default dashboard config


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = default_dashboard_config()
cfg.format = "html"
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
expect(result.html_output).to_contain("DOCTYPE")
```

</details>

#### html output contains dashboard heading

1. var cfg = default dashboard config


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = default_dashboard_config()
cfg.format = "html"
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
expect(result.html_output).to_contain("Dashboard")
```

</details>

#### both format

#### produces both text and html output

1. var cfg = default dashboard config
   - Expected: text_len > 0 is true
   - Expected: html_len > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = default_dashboard_config()
cfg.format = "both"
val summary = build_test_summary()
val req = DashboardRenderRequest(config: cfg, summary: summary)
val result = render_dashboard(req)
val text_len = result.text_output.len()
val html_len = result.html_output.len()
expect(text_len > 0).to_equal(true)
expect(html_len > 0).to_equal(true)
```

</details>

### Office Render Adapter Routing

#### unknown adapter_name

#### returns text mentioning unknown adapter

1. var cfg = RenderConfig default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = RenderConfig.default()
cfg.adapter_name = "nonexistent_app"

val result = office_render(cfg)
expect(result.text_output).to_contain("Unknown")
```

</details>

#### includes warning for unknown adapter

1. var cfg = RenderConfig default
   - Expected: has_warnings is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = RenderConfig.default()
cfg.adapter_name = "nonexistent_app"

val result = office_render(cfg)
val has_warnings = result.warnings.len() > 0
expect(has_warnings).to_equal(true)
```

</details>

#### known adapter names route correctly

#### word adapter produces non-empty text output

1. var cfg = RenderConfig default
   - Expected: len > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = RenderConfig.default()
cfg.adapter_name = "word"

val result = office_render(cfg)
val len = result.text_output.len()
expect(len > 0).to_equal(true)
```

</details>

#### word adapter text output contains app name

1. var cfg = RenderConfig default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = RenderConfig.default()
cfg.adapter_name = "word"

val result = office_render(cfg)
expect(result.text_output).to_contain("Word")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/ui_render_feature_caret.md](doc/05_design/ui_render_feature_caret.md)


</details>
