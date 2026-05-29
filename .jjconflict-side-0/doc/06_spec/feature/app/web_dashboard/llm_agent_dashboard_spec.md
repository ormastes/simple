# LLM Agent Dashboard Web Contracts

| Field | Value |
|---|---|
| Source | `test/feature/app/web_dashboard/llm_agent_dashboard_spec.spl` |
| Feature IDs | `#WEB-DASHBOARD-AGENTS` |
| Category | Application |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |

## Overview

This SPipe spec pins the web dashboard contracts that keep the agent dashboard
reachable only through authenticated routes and keep the generated dashboard UI
responsive on narrow screens.

## Scenario Summary

| Metric | Count |
|---|---:|
| Total scenarios | 2 |
| Active scenarios | 2 |

## Scenarios

### LLM agent dashboard web contracts

#### redirects unauthenticated /agents requests to /login

```simple
val source = _read_source(SERVER_PATH)
expect(source).to_contain("if clean_path == \"/agents\" or clean_path.starts_with(\"/agents\"):")
expect(source).to_contain("if session == nil:")
expect(source).to_contain("return http_redirect(\"/login\")")
```

#### includes responsive layout rules for narrow screens

```simple
val html_source = _read_source(HTML_VIEWS_PATH)
expect(html_source).to_contain("@media (max-width: 1100px)")
expect(html_source).to_contain("@media (max-width: 720px)")
expect(html_source).to_contain("grid-template-columns: 1fr 1fr 1fr")
expect(html_source).to_contain("grid-template-columns: 1fr 1fr")
expect(html_source).to_contain("grid-template-columns: 1fr;")
```
