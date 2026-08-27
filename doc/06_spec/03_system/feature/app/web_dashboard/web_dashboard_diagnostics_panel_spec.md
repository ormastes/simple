# Web Dashboard Diagnostics Panel Specification

> Tests covering web dashboard diagnostics panel readback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Dashboard Diagnostics Panel Specification

## Scenarios

### web dashboard diagnostics panel readback

#### embeds diagnostics panel markup in the dashboard shell

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- embeds diagnostics panel markup in the dashboard shell
   - Expected: html.split("switchView('tooling', this)").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("embeds diagnostics panel markup in the dashboard shell")
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
expect(html.split("switchView('tooling', this)").len()).to_equal(1)
```

</details>

#### embeds tooling artifacts in a dedicated dashboard view

- embeds tooling artifacts in a dedicated dashboard view


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("embeds tooling artifacts in a dedicated dashboard view")
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

- renders authenticated HTTP dashboard with diagnostics JSONL readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders authenticated HTTP dashboard with diagnostics JSONL readback")
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
expect_absence_marker_hidden(response)
remove_file_if_exists(path)
```

</details>

#### renders missing diagnostics fields as explicit none markers

- renders missing diagnostics fields as explicit none markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders missing diagnostics fields as explicit none markers")
val path = diagnostics_panel_fixture_path()
mkdir_p(".build/llm_dashboard/diagnostics")
remove_file_if_exists(path)
write_file(path, "{\"ts\":1710000000200,\"data\":{}}\n")
val server = DashboardServer.new_with_diagnostics(4242, path)
val response = server.route_http("GET", "/", "", "simple-dashboard-session")
expect(response).to_contain("events=1")
expect(response).to_contain("last_event=none")
expect(response).to_contain("last_session=none")
expect_absence_marker_hidden(response)
remove_file_if_exists(path)
```

</details>

#### renders configured context and ponytail tooling panel

- renders configured context and ponytail tooling panel
   - Expected: diagnostics_view.split("llm-tooling-artifacts-panel").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders configured context and ponytail tooling panel")
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
expect(diagnostics_view.split("llm-tooling-artifacts-panel").len()).to_equal(1)
expect(response).to_contain("LLM Tooling Artifacts")
expect(response).to_contain("context_status=ready")
expect(response).to_contain("ponytail_status=review")
expect(response).to_contain("FutureThing")
expect_absence_marker_hidden(response)
remove_file_if_exists(diagnostics_path)
remove_file_if_exists(tooling_path)
```

</details>

#### renders missing tooling source as explicit absence

- renders missing tooling source as explicit absence


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders missing tooling source as explicit absence")
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
expect_absence_marker_hidden(response)
remove_file_if_exists(diagnostics_path)
```

</details>

#### keeps the operator guide aligned with diagnostics, tooling, and vLLM panels

- keeps the operator guide aligned with diagnostics, tooling, and vLLM panels


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the operator guide aligned with diagnostics, tooling, and vLLM panels")
val guide = file_read("doc/07_guide/app/dashboard.md")

expect(guide).to_contain("Web Dashboard")
expect(guide).to_contain("view-diagnostics")
expect(guide).to_contain("view-tooling")
expect(guide).to_contain("llm-tooling-artifacts-panel")
expect(guide).to_contain("/api/vllm/control")
expect(guide).to_contain("simple_context")
expect(guide).to_contain("simple_ponytail")
expect_absence_marker_hidden(guide)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering web dashboard diagnostics panel readback.
- web dashboard diagnostics panel readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `321d57f1ea36e78b20149b09a77d285ce88c10e97ffd53b0d37cf4300f7fcfa5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `321d57f1ea36e78b20149b09a77d285ce88c10e97ffd53b0d37cf4300f7fcfa5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `321d57f1ea36e78b20149b09a77d285ce88c10e97ffd53b0d37cf4300f7fcfa5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl
mirror: doc/06_spec/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'embeds diagnostics panel markup in the dashboard shell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'embeds tooling artifacts in a dedicated dashboard view' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders authenticated HTTP dashboard with diagnostics JSONL readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
