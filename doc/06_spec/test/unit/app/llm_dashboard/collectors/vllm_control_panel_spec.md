# Vllm Control Panel Specification

> <details>

<!-- sdn-diagram:id=vllm_control_panel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_control_panel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_control_panel_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_control_panel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Control Panel Specification

## Scenarios

### LLM dashboard vLLM control panel

#### preflights configured vLLM controls without spawning

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = collect_llm_dashboard_vllm_control_preflight(fixture_vllm_manifest())
val text = render_llm_dashboard_vllm_control_panel_text(panel)

expect(panel.action).to_equal("preflight")
expect(panel.status).to_equal("planned")
expect(panel.reason).to_equal("serve_and_models_probe_planned")
expect(panel.pid).to_equal(-1)
expect(text).to_contain("vLLM Controls")
expect(text).to_contain("controls=preflight,start,poll,probe,stop")
expect(text.split("nil").len()).to_equal(1)
```

</details>

#### rejects unsupported dashboard control actions explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = collect_llm_dashboard_vllm_control_action(fixture_vllm_manifest(), "restart", 55)
val text = render_llm_dashboard_vllm_control_panel_text(panel)

expect(panel.status).to_equal("rejected")
expect(panel.reason).to_equal("unknown_action")
expect(panel.pid).to_equal(55)
expect(text).to_contain("action=restart")
expect(text.split("nil").len()).to_equal(1)
```

</details>

#### routes side-effecting action intent through runtime control decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = collect_llm_dashboard_vllm_control_action(fixture_vllm_manifest(), "start", -1)

expect(panel.action).to_equal("start")
expect(panel.status).to_equal("planned")
expect(panel.reason).to_equal("live_executor_required")
expect(panel.models_reason).to_equal("probe_not_run")
expect(panel.evidence_jsonl.split("nil").len()).to_equal(1)
```

</details>

#### rejects stop requests with invalid pids before live execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = collect_llm_dashboard_vllm_control_action(fixture_vllm_manifest(), "stop", 0)

expect(panel.action).to_equal("stop")
expect(panel.status).to_equal("not_stopped")
expect(panel.reason).to_equal("invalid_pid")
expect(panel.running_status).to_equal("not_running")
expect(panel.evidence_jsonl).to_contain("\"event\":\"llm_dashboard_vllm_control_panel\"")
expect(panel.evidence_jsonl.split("nil").len()).to_equal(1)
```

</details>

#### renders HTML controls for dashboard operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = collect_llm_dashboard_vllm_control_preflight(fixture_vllm_manifest())
val html = render_llm_dashboard_vllm_control_panel_html(panel)

expect(html).to_contain("id=\"llm-vllm-control-panel\"")
expect(html).to_contain("value=\"start\"")
expect(html).to_contain("value=\"probe\"")
expect(html).to_contain("serve_and_models_probe_planned")
expect(html.split("nil").len()).to_equal(1)
```

</details>

#### exposes authenticated web dashboard vLLM control API

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", fixture_vllm_manifest())
val response = server.route_http("GET", "/api/vllm/control?action=preflight", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(response.split("nil").len()).to_equal(1)
```

</details>

#### routes dashboard start through live executor without implicit resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", fixture_vllm_manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start", "", "sid")

expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(response).to_contain("\"started_pid\":-1")
expect(response.split("nil").len()).to_equal(1)
```

</details>

#### embeds the vLLM control panel in dashboard HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", fixture_vllm_manifest())
val html = server.render_dashboard_html()

expect(html).to_contain("llm-vllm-control-panel")
expect(html).to_contain("vLLM Controls")
expect(html).to_contain("serve_and_models_probe_planned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/collectors/vllm_control_panel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM dashboard vLLM control panel

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
