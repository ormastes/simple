# web_dashboard_html_shell_spec

> Verifies the generated HTML scaffold and the client-side routes

<!-- sdn-diagram:id=web_dashboard_html_shell_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_dashboard_html_shell_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_dashboard_html_shell_spec -> std
web_dashboard_html_shell_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_dashboard_html_shell_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_dashboard_html_shell_spec

Verifies the generated HTML scaffold and the client-side routes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/web_dashboard_html_shell_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the generated HTML scaffold and the client-side routes
    embedded in the dashboard page.

## Scenarios

### Web dashboard HTML shell

#### includes the expected outer document structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_full_dashboard_html(
    4242,
    "<section id=\"status-card\">status</section>",
    "main@abc123",
    "<div id=\"tmux-card\">tmux</div>",
    "<span>admin</span><a href=\"/logout\">Log out</a>"
)

expect(html).to_start_with("<!DOCTYPE html>")
expect html to_contain "<html lang=\"en\">"
expect html to_contain "<meta charset=\"utf-8\">"
expect html to_contain "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
expect html to_contain "<title>Simple Compiler Dashboard</title>"
expect html to_contain "<style>"
expect html to_contain "<script>"
expect html to_contain "</html>"
```

</details>

#### embeds the dashboard views and client routes

1. expect html to contain "switchView
2. expect html to contain "switchView
3. expect html to contain "fetch
4. expect html to contain "setTimeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_full_dashboard_html(
    4242,
    "<section id=\"status-card\">status</section>",
    "main@abc123",
    "<div id=\"tmux-card\">tmux</div>",
    "<span>admin</span><a href=\"/logout\">Log out</a>"
)

expect html to_contain "<div id=\"view-status\" class=\"view active\">"
expect html to_contain "<div id=\"view-terminal\" class=\"view\">"
expect html to_contain "<div id=\"view-gui\" class=\"view\">"
expect html to_contain "<section id=\"status-card\">status</section>"
expect html to_contain "<div id=\"tmux-card\">tmux</div>"
expect html to_contain "switchView('terminal', this)"
expect html to_contain "switchView('gui', this)"
expect html to_contain "window.location='/agents'"
expect html to_contain "fetch('/api/tmux/sessions')"
expect html to_contain "fetch('/api/tmux/windows?session='"
expect html to_contain "fetch('/api/tmux/panes?session='"
expect html to_contain "fetch('/api/tmux/capture?session='"
expect html to_contain "/ws/terminal?session="
expect html to_contain "<div class=\"header-identity\">"
expect html to_contain "<a href=\"/logout\">Log out</a>"
expect html to_contain "send-command"
expect html to_contain "setTimeout(() => location.reload(), 30000);"
```

</details>

#### keeps authenticated identity controls separate from the login screen

1. expect html contains
2. expect html contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_full_dashboard_html(
    4242,
    "<section id=\"status-card\">status</section>",
    "main@abc123",
    "<div id=\"tmux-card\">tmux</div>",
    "<span class=\"user\">alice</span><a href=\"/logout\">Log out</a>"
)

expect html to_contain "<div class=\"header-identity\">"
expect html to_contain "<span class=\"user\">alice</span>"
expect html to_contain "<a href=\"/logout\">Log out</a>"
expect html.contains("<form method=\"POST\" action=\"/login\">") to_equal false
expect html.contains("LLM Dashboard Login") to_equal false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
