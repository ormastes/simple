# vLLM Dashboard Control Route Specification

> This system spec verifies the authenticated web-dashboard control route for vLLM runtime operations. The route is intentionally split between pure dashboard planning and runtime-owned live execution so a web request cannot silently start processes, poll process state, fetch HTTP endpoints, or stop processes unless the response explicitly advertises that a runtime executor is required.

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
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vLLM Dashboard Control Route Specification

This system spec verifies the authenticated web-dashboard control route for vLLM runtime operations. The route is intentionally split between pure dashboard planning and runtime-owned live execution so a web request cannot silently start processes, poll process state, fetch HTTP endpoints, or stop processes unless the response explicitly advertises that a runtime executor is required.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/llm_runtime_vllm_torch_interface.md |
| Plan | doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md |
| Design | doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md |
| Research | doc/01_research/domain/llm_runtime_vllm_torch_interface.md |
| Source | `test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the authenticated web-dashboard control route for
vLLM runtime operations. The route is intentionally split between pure
dashboard planning and runtime-owned live execution so a web request cannot
silently start processes, poll process state, fetch HTTP endpoints, or stop
processes unless the response explicitly advertises that a runtime executor is
required.

The spec covers three boundaries:

- `preflight` stays on the dashboard-safe collector and returns plan evidence.
- `start`, `poll`, `probe`, and `stop` return runtime-owned JSONL evidence.
- Live-capable inputs still return `requires_runtime_executor=true` rather
  than importing or calling the live executor from the route.

## Syntax

Authenticated dashboard control route:

```text
GET /api/vllm/control?action=<preflight|start|poll|probe|stop>&pid=<pid>&vllm_available=<bool>&gpu_available=<bool>
```

Optional query overrides:

```text
base_model=<redacted model id>
endpoint=http://127.0.0.1:8000/v1
```

The response is JSONL. Public output must redact model identifiers, must render
missing local resources as explicit status/reason fields, and must not leak
implementation-level absence markers.

## Examples

Missing local vLLM:

```text
GET /api/vllm/control?action=start&vllm_available=false&gpu_available=true
```

Expected JSONL fields:

```json
{"action":"start","status":"skipped","reason":"missing_local_vllm","requires_runtime_executor":false}
```

Local vLLM and GPU available:

```text
GET /api/vllm/control?action=start&vllm_available=true&gpu_available=true
```

Expected JSONL fields:

```json
{"action":"start","status":"planned","reason":"live_executor_required","requires_runtime_executor":true}
```

This is not live evidence. It proves the dashboard route knows a runtime owner
must perform the side effect and leaves the side effect outside the web route.

## Evidence Matrix

| Boundary | Evidence in this spec |
|----------|-----------------------|
| Auth | Unauthenticated `/api/vllm/control` returns `401`. |
| Redaction | Model overrides do not appear in route output. |
| Missing resources | Start requests return skipped JSONL without executor requirement. |
| Live-capable resources | Start/poll/probe/stop return executor-required JSONL. |
| Ownership | Server imports the runtime boundary, not the live executor module. |

## Acceptance Notes

The dashboard route is allowed to assemble a manifest from query overrides and
to call the runtime boundary that emits safe JSONL. It is not allowed to call
the live executor module directly. That separation matters because live
execution can spawn `vllm`, inspect process state, fetch `/models`, or stop a
process. Those side effects belong to runtime-owned evidence wrappers where
resource checks, redaction, and host capability reporting are explicit.

The `requires_runtime_executor` field is the handoff flag. A value of `false`
means the route handled the request completely as planning or skipped evidence.
A value of `true` means the route found a live-capable intent, but the operator
or a runtime owner must run the live executor path to produce real live
evidence. This spec therefore does not claim a live vLLM server was started or
probed. It proves the route exposes the right boundary for a later live run.

The redaction checks use split-count assertions for the configured base model
and absence-marker helper assertions for public output. Generated manuals should
show the public behavior and helper names, not implementation sentinel values.

## Scenarios

### vLLM dashboard control web route

#### serves authenticated preflight control JSONL

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=false&gpu_available=true", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=true&gpu_available=false", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=false&gpu_available=false", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(response).to_contain("\"models_reason\":\"environment_skipped\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect_absence_marker_hidden(response)
```

</details>

#### routes live-capable side-effect actions as executor-required JSONL without importing the live executor

- expect absence marker hidden
- expect absence marker hidden
- expect absence marker hidden
- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_vllm_manifest(3099, "", "", "", _manifest())
val start_response = server.route_http("GET", "/api/vllm/control?action=start&vllm_available=true&gpu_available=true", "", "sid")
val poll_response = server.route_http("GET", "/api/vllm/control?action=poll&pid=123&vllm_available=true&gpu_available=true", "", "sid")
val probe_response = server.route_http("GET", "/api/vllm/control?action=probe&pid=123&vllm_available=true&gpu_available=true", "", "sid")
val stop_response = server.route_http("GET", "/api/vllm/control?action=stop&pid=123&vllm_available=true&gpu_available=true", "", "sid")
val server_source = _read_source(SERVER_PATH)

expect(start_response).to_contain("\"action\":\"start\"")
expect(start_response).to_contain("\"status\":\"planned\"")
expect(start_response).to_contain("\"reason\":\"live_executor_required\"")
expect(start_response).to_contain("\"requires_runtime_executor\":true")
expect(poll_response).to_contain("\"action\":\"poll\"")
expect(poll_response).to_contain("\"requires_runtime_executor\":true")
expect(probe_response).to_contain("\"action\":\"probe\"")
expect(probe_response).to_contain("\"requires_runtime_executor\":true")
expect(stop_response).to_contain("\"action\":\"stop\"")
expect(stop_response).to_contain("\"requires_runtime_executor\":true")
expect(server_source.split("dashboard_live_control_executor").len()).to_equal(1)
expect_absence_marker_hidden(start_response)
expect_absence_marker_hidden(poll_response)
expect_absence_marker_hidden(probe_response)
expect_absence_marker_hidden(stop_response)
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

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_source = _read_source(SERVER_PATH)
val collector_source = _read_source(COLLECTOR_PATH)
val runtime_boundary = _read_source(RUNTIME_BOUNDARY_PATH)
val live_executor = _read_source(LIVE_EXECUTOR_PATH)

expect(server_source).to_contain("collect_llm_dashboard_vllm_control_action_with_overrides")
expect(server_source).to_contain("llm_runtime_execute_dashboard_control_jsonl")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/llm_runtime_vllm_torch_interface.md](doc/02_requirements/nfr/llm_runtime_vllm_torch_interface.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md](doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md)
- **Design:** [doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md](doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md)
- **Research:** [doc/01_research/domain/llm_runtime_vllm_torch_interface.md](doc/01_research/domain/llm_runtime_vllm_torch_interface.md)


</details>
