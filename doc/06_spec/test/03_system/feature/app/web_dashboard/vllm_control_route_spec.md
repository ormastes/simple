# Vllm Control Route Specification

> <details>

<!-- sdn-diagram:id=vllm_control_route_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vllm_control_route_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vllm_control_route_spec -> std
vllm_control_route_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vllm_control_route_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Control Route Specification

## Scenarios

### vLLM dashboard control web route

#### serves authenticated preflight control JSONL

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=preflight", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("Content-Type: application/json")
expect(response).to_contain("\"event\":\"llm_dashboard_vllm_control_panel\"")
expect(response).to_contain("\"action\":\"preflight\"")
expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(response.contains("base-model")).to_equal(false)
expect(response.contains(_absence_marker())).to_equal(false)
```

</details>

#### rejects unauthenticated vLLM control API requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=preflight", "", "")

expect(response).to_contain("HTTP/1.1 401 Unauthorized")
expect(response).to_contain("Authentication required")
```

</details>

#### accepts query-style model and endpoint overrides without leaking model ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", "")
val response = server.route_http("GET", "/api/vllm/control?action=preflight&base_model=base-model&endpoint=http://127.0.0.1:8000/v1", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(response.contains("base-model")).to_equal(false)
expect(response.contains(_absence_marker())).to_equal(false)
```

</details>

#### returns skipped evidence when query-style resource flags report missing vLLM

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=false&gpu_available=true", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect(response.contains(_absence_marker())).to_equal(false)
```

</details>

#### embeds the vLLM control panel in authenticated dashboard HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("id=\"llm-vllm-control-panel\"")
expect(response).to_contain("action=\"/api/vllm/control\"")
expect(response).to_contain("value=\"start\"")
expect(response).to_contain("value=\"probe\"")
expect(response.contains(_absence_marker())).to_equal(false)
```

</details>

#### keeps the web route on the dashboard-safe collector boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_source = _read_source(SERVER_PATH)
val collector_source = _read_source(COLLECTOR_PATH)
val runtime_boundary = _read_source(RUNTIME_BOUNDARY_PATH)

expect(server_source).to_contain("collect_llm_dashboard_vllm_control_action_with_overrides")
expect(server_source).to_contain("if path.starts_with(\"/api/vllm/control\")")
expect(server_source).to_contain("vllm_available")
expect(server_source).to_contain("gpu_available")
expect(server_source.contains("dashboard_live_control_executor")).to_equal(false)
expect(collector_source).to_contain("llm_runtime_execute_dashboard_control")
expect(runtime_boundary).to_contain("process_access")
expect(runtime_boundary).to_contain("http_access")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- vLLM dashboard control web route

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
