# vLLM Dashboard Control Route Specification

> This system spec verifies the web dashboard `/api/vllm/control` route. The route must authenticate operator requests, accept query-style control inputs, redact model identifiers, and keep ordinary dashboard rendering separated from live process and HTTP ownership.

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

# vLLM Dashboard Control Route Specification

This system spec verifies the web dashboard `/api/vllm/control` route. The route must authenticate operator requests, accept query-style control inputs, redact model identifiers, and keep ordinary dashboard rendering separated from live process and HTTP ownership.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md |
| Plan | doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md |
| Design | doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md |
| Research | doc/01_research/local/llm_runtime_vllm_torch_interface.md |
| Source | `test/03_system/feature/app/web_dashboard/vllm_control_route_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the web dashboard `/api/vllm/control` route. The
route must authenticate operator requests, accept query-style control inputs,
redact model identifiers, and keep ordinary dashboard rendering separated from
live process and HTTP ownership.

Preflight remains dashboard-safe intent evidence. Side-effecting actions
(`start`, `poll`, `probe`, and `stop`) return runtime-owned JSONL evidence
through the vLLM runtime boundary. Missing-resource and invalid-pid examples
must stay side-effect free and explicitly report
`live_evidence_status=not_live_evidence`.

## Syntax

```text
GET /api/vllm/control?action=preflight
GET /api/vllm/control?action=start&vllm_available=false&gpu_available=true
GET /api/vllm/control?action=poll&pid=0&vllm_available=true&gpu_available=true
```

Authenticated responses are JSONL payloads embedded in an HTTP 200 response.
Unauthenticated requests return HTTP 401. These route checks do not start
`vllm`, fetch `/v1/models`, or prove GPU serving readiness.

## Expected Evidence

- preflight: `llm_dashboard_vllm_control_panel`
- side-effecting blocked actions:
  `llm_runtime_vllm_dashboard_control_execution`
- non-live route examples:
  `live_evidence_status=not_live_evidence`
- live endpoint proof is reserved for runtime-owner observation evidence with
  a running process, ready models status, and 2xx HTTP status.

## Route Matrix

Authenticated `preflight` requests stay on the dashboard-safe collector facade.
They may use configured manifest text or query-style `base_model` and
`endpoint` overrides. The route returns planned intent evidence and
`requires_runtime_executor=false`.

Authenticated `start` requests are side-effecting in principle, so the route
uses runtime-owner execution JSONL. The scenarios in this spec pass explicit
missing-resource flags to prove no process spawn occurs:

```text
action=start&vllm_available=false&gpu_available=true  -> missing_local_vllm
action=start&vllm_available=true&gpu_available=false  -> missing_local_gpu
action=start&vllm_available=false&gpu_available=false -> missing_local_vllm_and_gpu
```

Authenticated `poll`, `probe`, and `stop` requests also return runtime-owner
execution JSONL. The spec uses `pid=0` or invalid pid values so the route can
prove invalid-pid classification without touching host processes:

```text
action=poll&pid=0  -> not_ready / invalid_pid
action=probe&pid=0 -> not_ready / invalid_pid
action=stop&pid=0  -> not_stopped / invalid_pid
```

Unauthenticated requests must return HTTP 401 before any vLLM control logic
runs.

## Redaction Rules

The response must not expose the configured base model id in public JSONL or
HTML when the model can be treated as sensitive or path-like. These scenarios
assert the sample `base-model` appears zero times in response bodies.

The response must not render the internal absence marker. Missing resources,
missing pids, absent live evidence, and omitted optional values must use public
domain states such as `missing_local_vllm`, `invalid_pid`, `not_used`, `none`,
or `not_live_evidence`.

The route must not expose prompts, generated assistant content, adapter paths,
endpoint credentials, API keys, or private file paths. This route does not
create chat-completion payloads, but the same evidence redaction policy applies
to all dashboard-visible vLLM runtime data.

## Boundary Rules

Dashboard rendering may import the vLLM control panel collector and the pure
runtime control decision helper. It must not import the live executor into the
normal dashboard render path. The source-level scenario checks that
`src/app/web_dashboard/server.spl` does not directly import
`dashboard_live_control_executor` while still forwarding side-effect actions
through `llm_runtime_execute_dashboard_control_jsonl`.

The runtime owner owns live process and HTTP operations. A route response is
live endpoint evidence only when it is produced from a runtime observation with:

```text
process running
/v1/models status ready
HTTP status 2xx
```

All planned, skipped, rejected, unauthenticated, and invalid-pid route outputs
remain `not_live_evidence`.

## Operator Workflow

1. Open the authenticated dashboard and confirm the `llm-vllm-control-panel`
   is present.
2. Run preflight first. A planned preflight confirms the manifest shape and
   request planning path, not installed vLLM readiness.
3. If local vLLM or GPU resources are missing, expect explicit skipped
   runtime JSONL from `start` or `probe`.
4. If a process id is unknown or invalid, use `poll`, `probe`, or `stop` with
   that pid and expect an invalid-pid JSONL status without process teardown.
5. Treat `not_live_evidence` as a hard boundary. Do not cite these route
   examples as proof that a model endpoint is serving.

## Maintenance Notes

When dashboard route behavior changes, update this system spec and regenerate
both generated manual copies under `doc/06_spec/test/03_system/...` and
`doc/06_spec/03_system/...`. The canonical and test-path manuals must stay in
sync because operators read both locations in different workflows.

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

Runnable source: 11 lines folded for reproduction.
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
expect(response).to_contain("\"live_evidence_status\":\"not_live_evidence\"")
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
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_gpu\"")
expect(response).to_contain("\"models_reason\":\"environment_skipped\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect(response).to_contain("\"live_evidence_status\":\"not_live_evidence\"")
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
expect(response).to_contain("\"event\":\"llm_runtime_vllm_dashboard_control_execution\"")
expect(response).to_contain("\"action\":\"start\"")
expect(response).to_contain("\"status\":\"skipped\"")
expect(response).to_contain("\"reason\":\"missing_local_vllm_and_gpu\"")
expect(response).to_contain("\"models_reason\":\"environment_skipped\"")
expect(response).to_contain("\"requires_runtime_executor\":false")
expect(response).to_contain("\"live_evidence_status\":\"not_live_evidence\"")
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
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md](doc/02_requirements/feature/llm_runtime_vllm_torch_interface.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md](doc/03_plan/agent_tasks/llm_runtime_vllm_torch_interface.md)
- **Design:** [doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md](doc/05_design/app/tools/llm_runtime_vllm_torch_interface.md)
- **Research:** [doc/01_research/local/llm_runtime_vllm_torch_interface.md](doc/01_research/local/llm_runtime_vllm_torch_interface.md)


</details>
