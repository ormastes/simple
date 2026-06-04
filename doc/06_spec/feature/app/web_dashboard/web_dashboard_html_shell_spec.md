# Web Dashboard HTML Shell

| Field | Value |
|---|---|
| Source | `test/03_system/feature/app/web_dashboard/web_dashboard_html_shell_spec.spl` |
| Feature IDs | `#WEB-DASHBOARD-HTML` |
| Category | Application |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |

## Overview

This SPipe spec verifies the server-rendered dashboard HTML scaffold, embedded
views, client routes, and authenticated identity controls.

## Scenario Summary

| Metric | Count |
|---|---:|
| Total scenarios | 3 |
| Active scenarios | 3 |

## Scenarios

### Web dashboard HTML shell

#### includes the expected outer document structure

```simple
val html = generate_full_dashboard_html(4242, "<section id=\"status-card\">status</section>", "main@abc123", "<div id=\"tmux-card\">tmux</div>", "<span>admin</span><a href=\"/logout\">Log out</a>")
expect html to_start_with "<!DOCTYPE html>"
expect html to_contain "<html lang=\"en\">"
expect html to_contain "<meta charset=\"utf-8\">"
expect html to_contain "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
expect html to_contain "<title>Simple Compiler Dashboard</title>"
expect html to_contain "<style>"
expect html to_contain "<script>"
expect html to_contain "</html>"
```

#### embeds the dashboard views and client routes

```simple
val html = generate_full_dashboard_html(4242, "<section id=\"status-card\">status</section>", "main@abc123", "<div id=\"tmux-card\">tmux</div>", "<span>admin</span><a href=\"/logout\">Log out</a>")
expect html to_contain "<div id=\"view-status\" class=\"view active\">"
expect html to_contain "<div id=\"view-terminal\" class=\"view\">"
expect html to_contain "<div id=\"view-gui\" class=\"view\">"
expect html to_contain "switchView('terminal', this)"
expect html to_contain "fetch('/api/tmux/sessions')"
expect html to_contain "/ws/terminal?session="
expect html to_contain "<a href=\"/logout\">Log out</a>"
```

#### keeps authenticated identity controls separate from the login screen

```simple
val html = generate_full_dashboard_html(4242, "<section id=\"status-card\">status</section>", "main@abc123", "<div id=\"tmux-card\">tmux</div>", "<span class=\"user\">alice</span><a href=\"/logout\">Log out</a>")
expect html to_contain "<div class=\"header-identity\">"
expect html to_contain "<span class=\"user\">alice</span>"
expect html to_contain "<a href=\"/logout\">Log out</a>"
expect html.contains("<form method=\"POST\" action=\"/login\">") to_equal false
expect html.contains("LLM Dashboard Login") to_equal false
```
