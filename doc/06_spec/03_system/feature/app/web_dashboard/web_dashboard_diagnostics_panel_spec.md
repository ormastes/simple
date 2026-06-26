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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Dashboard Diagnostics Panel Specification

## Scenarios

### web dashboard diagnostics panel readback

#### embeds diagnostics panel markup in the dashboard shell

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
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
expect(html.contains("switchView('tooling', this)")).to_equal(false)
```

</details>

#### embeds tooling artifacts in a dedicated dashboard view

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_full_dashboard_html_with_diagnostics_and_tooling(
    4242,
    "<section id=\"status-card\">status</section>",
    "main@abc123",
    "<div id=\"tmux-card\">tmux</div>",
    "<span>admin</span>",
    "<section id=\"llm-diagnostics-panel\"><h2>LLM Diagnostics</h2></section>",
    "<section id=\"llm-tooling-artifacts-panel\"><h2>LLM Tooling Artifacts</h2></section>"
)
expect(html).to_contain("switchView('tooling', this)")
expect(html).to_contain("<div id=\"view-tooling\" class=\"view\">")
expect(html).to_contain("LLM Tooling Artifacts")
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
expect(response.contains(internal_absence_marker())).to_equal(false)
remove_file_if_exists(path)
```

</details>

#### renders missing diagnostics fields as explicit none markers

- mkdir p
- remove file if exists
- write file
   - Expected: response does not expose the internal absence marker
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
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
expect(response.contains(internal_absence_marker())).to_equal(false)
remove_file_if_exists(path)
```

</details>

#### renders configured context and ponytail tooling panel

- mkdir p
- remove file if exists
- write file
   - Expected: diagnostics view does not contain the tooling artifact panel
   - Expected: response does not expose the internal absence marker
- remove file if exists
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics_path = diagnostics_panel_fixture_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(diagnostics_path)
write_file(diagnostics_path, diagnostics_panel_fixture_jsonl())
val tooling_path = write_tooling_panel_fixture("tooling_ready", "interface FutureThing:\n    pass_todo\n")
val server = DashboardServer.new_with_diagnostics_and_tooling(4242, diagnostics_path, tooling_path, "FutureThing")
val response = server.route_http("GET", "/", "", "simple-dashboard-session")
val diagnostics_start = response.find("<div id=\"view-diagnostics\" class=\"view\">")
val tooling_start = response.find("<div id=\"view-tooling\" class=\"view\">")
val diagnostics_view = response.slice(diagnostics_start, tooling_start)

expect(response).to_contain("<section id=\"llm-tooling-artifacts-panel\">")
expect(response).to_contain("switchView('tooling', this)")
expect(response).to_contain("<div id=\"view-tooling\" class=\"view\">")
expect(diagnostics_view.contains("llm-tooling-artifacts-panel")).to_equal(false)
expect(response).to_contain("LLM Tooling Artifacts")
expect(response).to_contain("context_status=ready")
expect(response).to_contain("ponytail_status=review")
expect(response).to_contain("FutureThing")
expect(response.contains(internal_absence_marker())).to_equal(false)
remove_file_if_exists(diagnostics_path)
remove_file_if_exists(tooling_path)
```

</details>

#### renders missing tooling source as explicit absence

- mkdir p
- remove file if exists
- write file
- remove file if exists
   - Expected: response does not expose the internal absence marker
- remove file if exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics_path = diagnostics_panel_fixture_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(diagnostics_path)
write_file(diagnostics_path, diagnostics_panel_fixture_jsonl())
val tooling_path = tooling_panel_fixture_path("tooling_missing")
remove_file_if_exists(tooling_path)
val server = DashboardServer.new_with_diagnostics_and_tooling(4242, diagnostics_path, tooling_path, "missing")
val response = server.route_http("GET", "/", "", "simple-dashboard-session")

expect(response).to_contain("<section id=\"llm-tooling-artifacts-panel\">")
expect(response).to_contain("<div id=\"view-tooling\" class=\"view\">")
expect(response).to_contain("context_status=missing")
expect(response).to_contain("ponytail_status=missing")
expect(response).to_contain("ponytail_reason=source unavailable")
expect(response.contains(internal_absence_marker())).to_equal(false)
remove_file_if_exists(diagnostics_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl` |
| Updated | 2026-06-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web dashboard diagnostics panel readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
