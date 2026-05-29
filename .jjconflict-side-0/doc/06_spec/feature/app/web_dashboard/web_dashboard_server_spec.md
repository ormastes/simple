# Web Dashboard Server Router Contracts

| Field | Value |
|---|---|
| Source | `test/feature/app/web_dashboard/web_dashboard_server_spec.spl` |
| Feature IDs | `#WEB-DASHBOARD-SERVER` |
| Category | Application |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |

## Overview

This SPipe spec verifies the web dashboard router and authentication contracts
from source while the live browser-facing runtime path remains isolated.

## Scenario Summary

| Metric | Count |
|---|---:|
| Total scenarios | 7 |
| Active scenarios | 7 |

## Scenarios

### Web dashboard server router contracts

#### redirects unauthenticated requests for / to /login

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if session == nil:")
expect(source).to_contain("return http_redirect(\"/login\")")
```

#### serves the login page on GET /login

```simple
val server_source = _read_source(SERVER_PATH)
val login_source = _read_source(LOGIN_PATH)
expect(server_source).to_contain("if clean_path == \"/login\":")
expect(server_source).to_contain("return self.handle_login(method, body, session)")
expect(login_source).to_contain("LLM Dashboard Login")
expect(login_source).to_contain("<form method=\"POST\" action=\"/login\">")
```

#### rejects empty login submissions without minting an authenticated session

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if method != \"POST\":")
expect(source).to_contain("val auth_result = auth_authenticate_form(body)")
expect(source).to_contain("return http_response(401, \"text/html\", auth_login_page(")
```

#### logout clears any active session and returns to /login

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if clean_path == \"/logout\":")
expect(source).to_contain("return self.handle_logout(session)")
expect(source).to_contain("auth_clear_cookie_header(")
```

#### rejects unauthenticated API access

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if clean_path.starts_with(\"/api/\"):")
expect(source).to_contain("return http_error(401, \"Authentication required\")")
```

#### rejects unauthenticated terminal and tmux capture access on deeper routes

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if is_ws and path.starts_with(\"/ws/terminal\"):")
expect(source).to_contain("if path.starts_with(\"/api/tmux\"):")
expect(source).to_contain("return http_error(503, \"Tmux API is unavailable in this runtime mode\")")
```

#### routes unknown paths to the login redirect when unauthenticated

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if val active_session = session:")
expect(source).to_contain("http_redirect(\"/login\")")
```
