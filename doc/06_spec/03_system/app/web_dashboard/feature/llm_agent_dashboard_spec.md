# LLM Agent Dashboard Web Specification

> This system spec verifies the `/agents` web-dashboard route used by the LLM agent dashboard. The route must be protected by dashboard authentication, render an absence-safe dashboard for authenticated users, and avoid hijacking unrelated URL prefixes such as `/agentship`.

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

# LLM Agent Dashboard Web Specification

This system spec verifies the `/agents` web-dashboard route used by the LLM agent dashboard. The route must be protected by dashboard authentication, render an absence-safe dashboard for authenticated users, and avoid hijacking unrelated URL prefixes such as `/agentship`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/app/dashboard/kairos_like_simple_mcp_llm_dashboard.md |
| Plan | doc/03_plan/agent_tasks/kairos_like_simple_mcp_llm_dashboard.md |
| Design | doc/05_design/app/ui/kairos_like_simple_mcp_llm_dashboard.md |
| Research | doc/01_research/app/dashboard/kairos_like_simple_mcp_llm_dashboard_2026-04-15_local.md |
| Source | `test/03_system/feature/app/web_dashboard/llm_agent_dashboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the `/agents` web-dashboard route used by the LLM
agent dashboard. The route must be protected by dashboard authentication,
render an absence-safe dashboard for authenticated users, and avoid hijacking
unrelated URL prefixes such as `/agentship`.

The spec also verifies that the main dashboard shell links to `/agents`, so the
operator-facing entry point remains discoverable after dashboard HTML changes.

## Route Contract

Unauthenticated or blank-session requests to `/agents` redirect to `/login`.
Authenticated requests return HTTP 200 with the agent dashboard root element:

```text
id="agent-dashboard"
```

When no selected agent session exists, the dashboard must render explicit
domain text:

```text
selected session unavailable
```

It must not expose the internal absence marker or literal implementation
absence values in public HTML.

## Syntax

The route is served by `DashboardServer.route_http` in system tests and by the
web dashboard HTTP server in operator runs:

```text
GET /agents
GET /agents?view=live
GET /agents/<session-or-subroute>
```

Session state is supplied by the dashboard authentication layer. A missing or
blank session id is unauthorized. A non-empty authenticated session id allows
the dashboard to render the agent view even when no selected agent session is
available yet.

The dashboard shell entry is JavaScript-backed:

```text
window.location='/agents'
```

That entry point is intentionally checked at source level so shell navigation
cannot drift away from the route.

## Prefix Contract

The route match is exact for `/agents` and scoped for `/agents/...`. A similarly
named route such as `/agentship` must fall through to ordinary dashboard
handling and must not render the agent dashboard. This prevents broad prefix
matches from stealing unrelated future routes.

## Examples

Unauthenticated request:

```text
GET /agents
HTTP/1.1 302 Found
Location: /login
```

Blank-session request:

```text
GET /agents?view=live
HTTP/1.1 302 Found
Location: /login
```

Authenticated request with no selected agent:

```text
GET /agents
HTTP/1.1 200 OK
id="agent-dashboard"
selected session unavailable
```

Non-agent prefix:

```text
GET /agentship
HTTP/1.1 200 OK
```

The `/agentship` response must not contain `id="agent-dashboard"`.

## Operator Workflow

1. Visit `/` after authentication and use the dashboard shell entry for agents.
2. Visit `/agents` while authenticated to inspect live agent/session state.
3. If no selected session exists, treat `selected session unavailable` as a
   normal empty-state result, not as a server error.
4. If a request redirects to `/login`, establish a dashboard session before
   retrying the route.

## Maintenance Notes

Keep the route predicate in `src/app/web_dashboard/server.spl` narrow:

```text
path == "/agents" or path.starts_with("/agents/")
```

If the dashboard shell navigation changes, update this spec alongside
`src/app/web_dashboard/dashboard_html.spl` so the generated manual remains the
operator source of truth.

## Evidence Interpretation

Passing this spec proves route authentication, prefix matching, empty-state
rendering, absence-safe HTML, and shell navigation linkage. It does not prove a
live LLM session is running, that external LLM providers are reachable, or that
all dashboard panels have current data. Those live/session claims require their
own collector and provider evidence.

When this spec fails, inspect the failing category first:

- redirect failures usually indicate authentication/session handling drift
- missing `id="agent-dashboard"` indicates route rendering drift
- `/agentship` failures indicate an over-broad route predicate
- shell-link failures indicate dashboard navigation drift
- absence-marker failures indicate public empty-state rendering drift

## Scenarios

### LLM agent dashboard web contracts

#### redirects unauthenticated /agents requests to /login

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_agent_dir(3099, ".build/llm_dashboard/agent-system-empty")
val response = server.route_http("GET", "/agents", "", no_session_id())

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/app/dashboard/kairos_like_simple_mcp_llm_dashboard.md](doc/02_requirements/app/dashboard/kairos_like_simple_mcp_llm_dashboard.md)
- **Plan:** [doc/03_plan/agent_tasks/kairos_like_simple_mcp_llm_dashboard.md](doc/03_plan/agent_tasks/kairos_like_simple_mcp_llm_dashboard.md)
- **Design:** [doc/05_design/app/ui/kairos_like_simple_mcp_llm_dashboard.md](doc/05_design/app/ui/kairos_like_simple_mcp_llm_dashboard.md)
- **Research:** [doc/01_research/app/dashboard/kairos_like_simple_mcp_llm_dashboard_2026-04-15_local.md](doc/01_research/app/dashboard/kairos_like_simple_mcp_llm_dashboard_2026-04-15_local.md)


</details>
