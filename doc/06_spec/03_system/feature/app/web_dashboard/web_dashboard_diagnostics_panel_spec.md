# Web Dashboard Diagnostics Panel Specification

> <details>

<!-- sdn-diagram:id=web_dashboard_diagnostics_panel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_dashboard_diagnostics_panel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_dashboard_diagnostics_panel_spec -> app
web_dashboard_diagnostics_panel_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_dashboard_diagnostics_panel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Dashboard Diagnostics Panel Specification

## Scenarios

### web dashboard diagnostics panel readback

#### embeds diagnostics panel markup in the dashboard shell

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_full_dashboard_html_with_diagnostics(
    4242,
    "<section id=\"status-card\">status</section>",
    "main@abc123",
    "<div id=\"tmux-card\">tmux</div>",
    "<span>admin</span>",
    "<section id=\"llm-diagnostics-panel\"><h2>LLM Diagnostics</h2><p>events=2</p></section>"
)
expect(html).to_contain("switchView('diagnostics', this)")
expect(html).to_contain("<div id=\"view-diagnostics\" class=\"view\">")
expect(html).to_contain("LLM Diagnostics")
```

</details>

#### renders authenticated HTTP dashboard with diagnostics JSONL readback

- mkdir p
- remove file if exists
- write file
   - Expected: response does not expose the internal absence marker
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = diagnostics_panel_fixture_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, diagnostics_panel_fixture_jsonl())
val server = DashboardServer.new_with_diagnostics(4242, path)
val response = server.route_http("GET", "/", "", "simple-dashboard-session")
expect(response).to_start_with("HTTP/1.1 200 OK")
expect(response).to_contain("Content-Type: text/html")
expect(response).to_contain("<section id=\"llm-diagnostics-panel\">")
expect(response).to_contain("events=2")
expect(response).to_contain("sessions=1")
expect(response).to_contain("tool_events=1")
expect(response).to_contain("last_session=sid-web")
expect(response.contains("nil")).to_equal(false)
remove_file_if_exists(path)
```

</details>

#### renders missing diagnostics fields as explicit none markers

- mkdir p
- remove file if exists
- write file
   - Expected: response contains `events=1`
   - Expected: response contains `last_event=none`
   - Expected: response contains `last_session=none`
   - Expected: response does not expose the internal absence marker
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = diagnostics_panel_fixture_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, "{\"ts\":1710000000200,\"data\":{}}\n")
val server = DashboardServer.new_with_diagnostics(4242, path)
val response = server.route_http("GET", "/", "", "simple-dashboard-session")
expect(response).to_contain("events=1")
expect(response).to_contain("last_event=none")
expect(response).to_contain("last_session=none")
expect(response.contains("nil")).to_equal(false)
remove_file_if_exists(path)
```

</details>

#### renders configured context and ponytail tooling panel

- writes diagnostics fixture JSONL
- writes a Simple source fixture for the tooling panel
- builds a dashboard server with diagnostics and tooling configuration
- verifies the authenticated dashboard response contains:
  - `llm-tooling-artifacts-panel`
  - `LLM Tooling Artifacts`
  - `context_status=ready`
  - `ponytail_status=review`
  - the selected target name
- verifies public output does not expose internal absence markers

#### renders missing tooling source as explicit absence

- writes diagnostics fixture JSONL
- removes the tooling source fixture
- builds a dashboard server with diagnostics and missing tooling configuration
- verifies the authenticated dashboard response contains:
  - `llm-tooling-artifacts-panel`
  - `context_status=missing`
  - `ponytail_status=missing`
  - `ponytail_reason=source unavailable`
- verifies public output does not expose internal absence markers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl` |
| Updated | 2026-06-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web dashboard diagnostics panel readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
