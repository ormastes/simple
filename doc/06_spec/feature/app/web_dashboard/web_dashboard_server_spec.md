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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Dashboard Server Specification

## Scenarios

### Web dashboard server router contracts

#### redirects unauthenticated requests for / to /login

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if not _session_authenticated(session):")
expect(source).to_contain("return http_redirect(\"/login\")")
```

</details>

#### treats blank session tokens as unauthenticated

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)

expect(source).to_contain("fn _session_authenticated(session: text?) -> bool:")
expect(source).to_contain("value.trim() != \"\"")
```

</details>

#### rejects unauthenticated API access

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if path.starts_with(\"/api/\"):")
expect(source).to_contain("return http_error(401, \"Authentication required\")")
```

</details>

#### serves authenticated tmux API placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if path.starts_with(\"/api/tmux\"):")
expect(source).to_contain("return http_response(200, \"application/json\", \"[]\")")
```

</details>

#### rejects unsupported authenticated methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if method != \"GET\":")
expect(source).to_contain("return http_error(401, \"Method not supported\")")
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
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
