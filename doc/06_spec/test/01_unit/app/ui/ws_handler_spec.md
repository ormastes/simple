# Ws Handler Specification

> <details>

<!-- sdn-diagram:id=ws_handler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ws_handler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ws_handler_spec -> std
ws_handler_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ws_handler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ws Handler Specification

## Scenarios

### ui.web.ws_handler

#### recognizes websocket upgrade headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Host: localhost\nUpgrade: websocket\nConnection: Upgrade\n"
expect(is_ws_upgrade_request(headers)).to_equal(true)
expect(is_ws_upgrade_request("Host: localhost\nConnection: keep-alive\n")).to_equal(false)
```

</details>

#### extracts the websocket key from request headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Host: localhost\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\n"
expect(extract_ws_key(headers)).to_equal("dGhlIHNhbXBsZSBub25jZQ==")
```

</details>

#### computes the RFC websocket accept hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_ws_accept("dGhlIHNhbXBsZSBub25jZQ==")).to_equal("s3pPLMBiTxaQ9kYGzzhZRbK+xOo=")
```

</details>

#### extracts bearer tokens from authorization headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Authorization: Bearer secret-token\n"
expect(_extract_bearer(headers, "/ui/ws")).to_equal("secret-token")
```

</details>

#### extracts bearer tokens from the websocket query string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/ui/ws?token=query-token&client=wm"
expect(_extract_bearer("", path)).to_equal("query-token")
```

</details>

#### prefers authorization headers over query parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Authorization: Bearer header-token\n"
val path = "/ui/ws?token=query-token"
expect(_extract_bearer(headers, path)).to_equal("header-token")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ws_handler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui.web.ws_handler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
