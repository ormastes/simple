# Llm Agent Dashboard Specification

> <details>

<!-- sdn-diagram:id=llm_agent_dashboard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_agent_dashboard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_agent_dashboard_spec -> std
llm_agent_dashboard_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_agent_dashboard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Agent Dashboard Specification

## Scenarios

### LLM agent dashboard web contracts

#### redirects unauthenticated /agents requests to /login

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_agent_dir(3099, ".build/llm_dashboard/agent-system-empty")
val response = server.route_http("GET", "/agents", "", nil)

expect(response).to_contain("HTTP/1.1 302 Found")
expect(response).to_contain("Location: /login")
```

</details>

#### rejects blank sessions for /agents

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_agent_dir(3099, ".build/llm_dashboard/agent-system-empty")
val response = server.route_http("GET", "/agents?view=live", "", "")

expect(response).to_contain("HTTP/1.1 302 Found")
expect(response).to_contain("Location: /login")
```

</details>

#### renders authenticated /agents as an absence-safe dashboard

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_agent_dir(3099, ".build/llm_dashboard/agent-system-empty")
val response = server.route_http("GET", "/agents", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("id=\"agent-dashboard\"")
expect(response).to_contain("selected session unavailable")
expect_absence_marker_hidden(response)
```

</details>

#### does not hijack non-agents prefixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_agent_dir(3099, ".build/llm_dashboard/agent-system-empty")
val response = server.route_http("GET", "/agentship", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response.split("id=\"agent-dashboard\"").len()).to_equal(1)
```

</details>

#### keeps the dashboard shell linked to /agents

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_source = _read_source(SERVER_PATH)
val html_source = _read_source(DASHBOARD_HTML_PATH)

expect(server_source).to_contain("fn _is_agents_path(path: text) -> bool:")
expect(server_source).to_contain("path == \"/agents\" or path.starts_with(\"/agents/\")")
expect(html_source).to_contain("window.location='/agents'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/llm_agent_dashboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM agent dashboard web contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
