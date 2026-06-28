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
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vllm Control Route Specification

## Scenarios

### vLLM dashboard control web route

#### serves authenticated preflight control JSONL

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=preflight", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("Content-Type: application/json")
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_live_boundary\"")
expect(response).to_contain("\"boundary_status\":\"intent-only\"")
expect(response).to_contain("\"acceptance_status\":\"not_live_evidence\"")
expect(response).to_contain("\"event\":\"llm_dashboard_vllm_control_panel\"")
expect(response).to_contain("\"action\":\"preflight\"")
expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect(response.split("base-model").len()).to_equal(1)
expect_absence_marker_hidden(response)
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

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", "")
val response = server.route_http("GET", "/api/vllm/control?action=preflight&base_model=base-model&endpoint=http://127.0.0.1:8000/v1", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"status\":\"planned\"")
expect(response).to_contain("\"reason\":\"serve_and_models_probe_planned\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect(response.split("base-model").len()).to_equal(1)
expect_absence_marker_hidden(response)
```

</details>

#### routes missing-resource start through runtime execution JSONL without spawning

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=false&gpu_available=true", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"boundary_status\":\"blocked\"")
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect_absence_marker_hidden(response)
```

</details>

#### routes missing GPU start through runtime execution JSONL without spawning

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=true&gpu_available=false", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"boundary_status\":\"blocked\"")
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_gpu\"")
expect(response).to_contain("\"models_reason\":\"environment_skipped\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect_absence_marker_hidden(response)
```

</details>

#### routes missing vLLM and GPU start through runtime execution JSONL without spawning

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=false&gpu_available=false", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"boundary_status\":\"blocked\"")
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(response).to_contain("\"models_reason\":\"environment_skipped\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect_absence_marker_hidden(response)
```

</details>

#### routes poll, probe, and stop through runtime execution JSONL with safe invalid-pid inputs

-  assert safe runtime action
-  assert safe runtime action
-  assert safe runtime action


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_safe_runtime_action("action=poll&pid=0&vllm_available=true&gpu_available=true", "poll", "not_ready", "invalid_pid")
_assert_safe_runtime_action("action=probe&pid=0&vllm_available=true&gpu_available=true", "probe", "not_ready", "invalid_pid")
_assert_safe_runtime_action("action=stop&pid=0&vllm_available=true&gpu_available=true", "stop", "not_stopped", "invalid_pid")
```

</details>

#### embeds the vLLM control panel in authenticated dashboard HTML

- expect absence marker hidden


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
expect_absence_marker_hidden(response)
```

</details>

#### keeps preflight on the collector and side-effect actions on runtime-owner execution JSONL

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_source = _read_source(SERVER_PATH)
val collector_source = _read_source(COLLECTOR_PATH)
val runtime_boundary = _read_source(RUNTIME_BOUNDARY_PATH)
val live_executor = _read_source(LIVE_EXECUTOR_PATH)

expect(server_source).to_contain("collect_llm_dashboard_vllm_control_action_with_overrides")
expect(server_source).to_contain("llm_runtime_execute_dashboard_control_jsonl")
expect(server_source).to_contain("llm_runtime_dashboard_live_boundary_jsonl")
expect(server_source).to_contain("_is_vllm_side_effect_action")
expect(server_source).to_contain("if path.starts_with(\"/api/vllm/control\")")
expect(server_source).to_contain("vllm_available")
expect(server_source).to_contain("gpu_available")
expect(server_source.split("dashboard_live_control_executor").len()).to_equal(1)
expect(collector_source).to_contain("llm_runtime_execute_dashboard_control")
expect(collector_source).to_contain("requires_runtime_executor")
expect(runtime_boundary).to_contain("process_access")
expect(runtime_boundary).to_contain("http_access")
expect(live_executor).to_contain("llm_runtime_execute_dashboard_control_live")
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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
