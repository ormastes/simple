# Simple Web Browser WebSocket Handler Hardening Specification

> Verifies selected Feature C and NFR C WebSocket upgrade parsing, canonical route gating, bearer extraction, query-token non-authorization, and frame bounds.

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
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Browser WebSocket Handler Hardening Specification

Verifies selected Feature C and NFR C WebSocket upgrade parsing, canonical route gating, bearer extraction, query-token non-authorization, and frame bounds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/simple_web_browser_production_hardening.md |
| Source | `test/01_unit/app/ui/ws_handler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies selected Feature C and NFR C WebSocket upgrade parsing, canonical
route gating, bearer extraction, query-token non-authorization, and frame bounds.

**Requirements:** doc/02_requirements/feature/simple_web_browser_production_hardening.md
**Requirements:** doc/02_requirements/nfr/simple_web_browser_production_hardening.md
**Traceability:** REQ-WEB-HARD-005, REQ-WEB-HARD-007, REQ-WEB-HARD-012, NFR-WEB-HARD-004, NFR-WEB-HARD-005, NFR-WEB-HARD-008, NFR-WEB-HARD-010

## Scenarios

### ui.web.ws_handler

#### recognizes websocket upgrade headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Host: localhost\nUpgrade: websocket\nConnection: Upgrade\n"
expect(is_ws_upgrade_request(headers)).to_be(true)
expect(is_ws_upgrade_request("Host: localhost\nConnection: keep-alive\n")).to_be(false)
val lowercase = "Host: localhost\nupgrade: websocket\nconnection: keep-alive, Upgrade\n"
expect(is_ws_upgrade_request(lowercase)).to_be(true)
val missing_connection_upgrade = "Host: localhost\nUpgrade: websocket\nConnection: keep-alive\n"
expect(is_ws_upgrade_request(missing_connection_upgrade)).to_be(false)
```

</details>

#### allows websocket upgrades only for GET

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_ws_upgrade_method_allowed("GET")).to_be(true)
expect(ui_web_ws_upgrade_method_allowed("POST")).to_be(false)
expect(ui_web_ws_upgrade_method_allowed("get")).to_be(false)
```

</details>

#### allows websocket upgrades only on the canonical ui route

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_ws_upgrade_path_allowed("/ui/ws")).to_be(true)
expect(ui_web_ws_upgrade_path_allowed("/ui/ws?client=wm")).to_be(true)
expect(ui_web_ws_upgrade_path_allowed("/ws")).to_be(false)
expect(ui_web_ws_upgrade_path_allowed("/api/state")).to_be(false)
```

</details>

#### extracts the websocket key from request headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Host: localhost\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\n"
expect(extract_ws_key(headers)).to_equal("dGhlIHNhbXBsZSBub25jZQ==")
val lowercase = "Host: localhost\nsec-websocket-key: lowercase-key\n"
expect(extract_ws_key(lowercase)).to_equal("lowercase-key")
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

#### rejects websocket query bearer tokens unless compatibility is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/ui/ws?token=query-token&client=wm"
expect(_extract_bearer("", path)).to_equal("")
expect(ui_web_extract_bearer_with_query_policy("", path, false)).to_equal("")
expect(ui_web_extract_bearer_with_query_policy("", path, true)).to_equal("query-token")
```

</details>

#### extracts and decodes compatibility query bearer tokens from any query position

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/ui/ws?client=wm&token=abc%252Edef%253Aghi"
expect(ui_web_extract_bearer_with_query_policy("", path, true)).to_equal("abc%2Edef%3Aghi")
```

</details>

#### extracts bearer tokens from websocket subprotocols before query fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Sec-WebSocket-Protocol: simple-ui, bearer.abc%252Edef%253Aghi\n"
val path = "/ui/ws?token=query-token"
expect(_extract_bearer(headers, path)).to_equal("abc%2Edef%3Aghi")
expect(ui_web_ws_response_protocol(headers)).to_equal("simple-ui")
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

#### keeps query bearer compatibility disabled from production env values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_query_token_allowed_from_env_value("")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("0")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("false")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("1")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value("true")).to_be(false)
expect(ui_web_query_token_allowed_from_env_value(" yes ")).to_be(false)
```

</details>

#### bounds unauthenticated request body sizes before transport reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_content_length("Content-Length: 42\n")).to_equal(42)
expect(ui_web_content_length("content-length: 17\n")).to_equal(17)
expect(ui_web_body_exceeds_unauth_limit("Content-Length: 8192\n")).to_be(false)
val too_large = UI_WEB_MAX_UNAUTH_BODY_BYTES + 1
expect(ui_web_body_exceeds_unauth_limit("Content-Length: {too_large}\n")).to_be(true)
```

</details>

#### bounds inbound websocket frame payload lengths before allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ui_web_ws_frame_payload_allowed(0)).to_be(true)
expect(ui_web_ws_frame_payload_allowed(UI_WEB_MAX_WS_FRAME_BYTES)).to_be(true)
expect(ui_web_ws_frame_payload_allowed(UI_WEB_MAX_WS_FRAME_BYTES + 1)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/simple_web_browser_production_hardening.md](doc/02_requirements/nfr/simple_web_browser_production_hardening.md)


</details>
