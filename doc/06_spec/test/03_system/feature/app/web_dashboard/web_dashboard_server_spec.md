# Web Dashboard Server Specification

> <details>

<!-- sdn-diagram:id=web_dashboard_server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_dashboard_server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_dashboard_server_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_dashboard_server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Dashboard Server Specification

## Scenarios

### Web dashboard server router contracts

#### redirects unauthenticated requests for / to /login

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if session == nil:")
expect(source).to_contain("return http_redirect(\"/login\")")
```

</details>

#### serves the login page on GET /login

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_source = _read_source(SERVER_PATH)
val login_source = _read_source(LOGIN_PATH)
expect(server_source).to_contain("if clean_path == \"/login\":")
expect(server_source).to_contain("return self.handle_login(method, body, session)")
expect(login_source).to_contain("LLM Dashboard Login")
expect(login_source).to_contain("<form method=\"POST\" action=\"/login\">")
expect(login_source.contains("/api/tmux/sessions")).to_equal(false)
expect(login_source.contains("/ws/terminal?session=")).to_equal(false)
```

</details>

#### rejects empty login submissions without minting an authenticated session

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if method != \"POST\":")
expect(source).to_contain("val auth_result = auth_authenticate_form(body)")
expect(source).to_contain("return http_response(status: 401, content_type: \"text/html\", body: auth_login_page(")
```

</details>

#### logout clears any active session and returns to /login

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if clean_path == \"/logout\":")
expect(source).to_contain("return self.handle_logout(session)")
expect(source).to_contain("auth_clear_cookie_header(")
```

</details>

#### rejects unauthenticated API access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if clean_path.starts_with(\"/api/\"):")
expect(source).to_contain("return http_error(401, \"Authentication required\")")
```

</details>

#### rejects unauthenticated terminal and tmux capture access on deeper routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if is_ws and path.starts_with(\"/ws/terminal\"):")
expect(source).to_contain("if path.starts_with(\"/api/tmux\"):")
expect(source).to_contain("return http_error(503, \"Tmux API is unavailable in this runtime mode\")")
```

</details>

#### routes unknown paths to the login redirect when unauthenticated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if val active_session = session:")
expect(source).to_contain("http_redirect(\"/login\")")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/web_dashboard_server_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Web dashboard server router contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
