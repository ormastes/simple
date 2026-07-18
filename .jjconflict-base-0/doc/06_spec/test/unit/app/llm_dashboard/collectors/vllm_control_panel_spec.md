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
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Control Panel Specification

## Scenarios

### LLM dashboard vLLM control panel

#### preflights configured vLLM controls without spawning

- expect absence marker hidden


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
expect(text).to_contain("pid=0")
expect(text).to_contain("controls=preflight,start,poll,probe,stop")
expect(panel.evidence_jsonl).to_contain("\"pid\":0")
expect(panel.evidence_jsonl.split("\"pid\":-1").len()).to_equal(1)
expect_absence_marker_hidden(text)
```

</details>

#### rejects unsupported dashboard control actions explicitly

- expect absence marker hidden


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
expect_absence_marker_hidden(text)
```

</details>

#### routes side-effecting action intent through runtime control decisions

- expect absence marker hidden


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
expect_absence_marker_hidden(panel.evidence_jsonl)
```

</details>

#### honors dashboard resource flags before side-effecting actions

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = collect_llm_dashboard_vllm_control_action_with_resources(fixture_vllm_manifest(), "start", -1, false, true)

expect(panel.action).to_equal("start")
expect(panel.status).to_equal("skipped")
expect(panel.reason).to_equal("missing_local_vllm")
expect(panel.running_status).to_equal("not_started")
expect_absence_marker_hidden(panel.evidence_jsonl)
```

</details>

#### applies dashboard base model and endpoint overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val panel = collect_llm_dashboard_vllm_control_action_with_overrides("", "preflight", -1, "base-model", "http://127.0.0.1:8000/v1", true, true)

expect(panel.action).to_equal("preflight")
expect(panel.status).to_equal("planned")
expect(panel.reason).to_equal("serve_and_models_probe_planned")
expect(panel.endpoint_status).to_equal("configured")
expect(panel.evidence_jsonl.split("base-model").len()).to_equal(1)
```

</details>

#### rejects stop requests with invalid pids before live execution

- expect absence marker hidden


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
expect_absence_marker_hidden(panel.evidence_jsonl)
```

</details>

#### renders HTML controls for dashboard operators

- expect absence marker hidden


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
expect(html).to_contain("<p>pid=0</p>")
expect(html).to_contain("serve_and_models_probe_planned")
expect_absence_marker_hidden(html)
```

</details>

#### exposes authenticated web dashboard vLLM control API

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", fixture_vllm_manifest())
val response = server.route_http("GET", "/api/vllm/control?action=preflight", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"event\":\"llm_dashboard_vllm_control_panel\"")
expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"pid\":0")
expect(response.split("\"pid\":-1").len()).to_equal(1)
expect_absence_marker_hidden(response)
```

</details>

#### accepts query-style dashboard control resource flags

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", fixture_vllm_manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=false&gpu_available=true", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm\"")
expect_absence_marker_hidden(response)
```

</details>

#### accepts query-style dashboard model and endpoint overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", "")
val response = server.route_http("GET", "/api/vllm/control?action=preflight&base_model=base-model&endpoint=http://127.0.0.1:8000/v1", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(response.split("base-model").len()).to_equal(1)
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
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
