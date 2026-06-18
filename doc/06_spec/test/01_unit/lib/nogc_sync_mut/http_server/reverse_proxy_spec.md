# Sync HTTP Reverse Proxy Helpers

> These scenarios verify the sync HTTP reverse proxy helper boundary. The sync path rewrites normal HTTP requests for a backend process, drops hop-by-hop headers, preserves CPU-owned HTTP control-plane behavior, and fails closed for unsupported request framing or Upgrade traffic before connecting upstream.

<!-- sdn-diagram:id=reverse_proxy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reverse_proxy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reverse_proxy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reverse_proxy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sync HTTP Reverse Proxy Helpers

These scenarios verify the sync HTTP reverse proxy helper boundary. The sync path rewrites normal HTTP requests for a backend process, drops hop-by-hop headers, preserves CPU-owned HTTP control-plane behavior, and fails closed for unsupported request framing or Upgrade traffic before connecting upstream.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | doc/02_requirements/feature/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_sync_mut/http_server/reverse_proxy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These scenarios verify the sync HTTP reverse proxy helper boundary. The sync
path rewrites normal HTTP requests for a backend process, drops hop-by-hop
headers, preserves CPU-owned HTTP control-plane behavior, and fails closed for
unsupported request framing or Upgrade traffic before connecting upstream.

## Requirements

**Requirements:** doc/02_requirements/feature/gpu_web_db_offload.md

- Sync proxy routes match only safe paths and supported HTTP methods.
- Hop-by-hop request and response headers are not forwarded.
- Fixed parsed request bodies are serialized with recomputed content length.
- Oversized fixed parsed request bodies are written to upstream in bounded
  slices instead of one full buffered request wire.
- Chunked request bodies fail closed until streaming support exists.
- Upgrade/WebSocket requests fail closed until bidirectional tunneling exists.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** N/A

## Examples

Register a sync reverse proxy route for a backend application, forward normal
fixed-length HTTP requests, stream oversized fixed bodies to upstream in
bounded slices, and reject chunked or Upgrade traffic until the server has real
chunked streaming/tunnel support.

## Scenarios

### sync HTTP reverse proxy helpers

#### should match safe proxy prefixes for supported methods

- Match GET requests on a configured proxy prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Match GET requests on a configured proxy prefix")
val route = reverse_proxy_route("/api/", "127.0.0.1:3000")
val req = proxy_req(HttpMethod.Get, "/api/users", "page=1", [])
expect(reverse_proxy_prefix_matches(route, req)).to_be(true)
expect(reverse_proxy_matches_request(route, req)).to_be(true)
```

</details>

#### should reject unsafe traversal paths before proxying

- Reject a traversal path that shares the proxy prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a traversal path that shares the proxy prefix")
val route = reverse_proxy_route("/api/", "127.0.0.1:3000")
val req = proxy_req(HttpMethod.Get, "/api/../secret", "", [])
expect(reverse_proxy_prefix_matches(route, req)).to_be(false)
```

</details>

#### should route normal HTTP methods through the proxy path

- Detect POST as supported for backend application forwarding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Detect POST as supported for backend application forwarding")
val route = reverse_proxy_route("/api/", "127.0.0.1:3000")
val req = proxy_req(HttpMethod.Post, "/api/users", "", [])
expect(reverse_proxy_prefix_matches(route, req)).to_be(true)
expect(reverse_proxy_matches_request(route, req)).to_be(true)
```

</details>

#### should detect unsupported chunked proxy request bodies

- Fail closed before stripping Transfer-Encoding from a request body
- [


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before stripping Transfer-Encoding from a request body")
val req = proxy_req_with_body(
    HttpMethod.Post,
    "/api/upload",
    "",
    [("Transfer-Encoding", "chunked")],
    "5\r\nhello\r\n0\r\n\r\n"
)
expect(reverse_proxy_request_transfer_chunked(req)).to_be(true)
```

</details>

#### should detect unsupported upgrade proxy requests

- Fail closed before stripping Upgrade headers from WebSocket traffic
- [


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail closed before stripping Upgrade headers from WebSocket traffic")
val req = proxy_req(
    HttpMethod.Get,
    "/api/ws",
    "",
    [("Connection", "keep-alive, Upgrade"), ("Upgrade", "websocket")]
)
expect(reverse_proxy_request_upgrade(req)).to_be(true)
```

</details>

#### should drop hop-by-hop and authority headers

- Classify headers that must not be forwarded


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify headers that must not be forwarded")
expect(reverse_proxy_drop_header("Connection")).to_be(true)
expect(reverse_proxy_drop_header("Transfer-Encoding")).to_be(true)
expect(reverse_proxy_drop_header("Upgrade")).to_be(true)
expect(reverse_proxy_drop_header("Host")).to_be(true)
expect(reverse_proxy_drop_header("Content-Length")).to_be(true)
expect(reverse_proxy_drop_header("Accept")).to_be(false)
```

</details>

#### should drop hop-by-hop response headers

- Classify upstream response headers that must not reach clients


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify upstream response headers that must not reach clients")
expect(reverse_proxy_drop_response_header("Connection")).to_be(true)
expect(reverse_proxy_drop_response_header("Transfer-Encoding")).to_be(true)
expect(reverse_proxy_drop_response_header("Upgrade")).to_be(true)
expect(reverse_proxy_drop_response_header("Content-Length")).to_be(false)
expect(reverse_proxy_drop_response_header("Content-Type")).to_be(false)
```

</details>

#### should validate upstream response status lines

- Reject malformed upstream status before forwarding it to the client


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject malformed upstream status before forwarding it to the client")
expect(reverse_proxy_status_line_valid("HTTP/1.1 200 OK")).to_be(true)
expect(reverse_proxy_status_line_valid("HTTP/1.0 204 No Content")).to_be(true)
expect(reverse_proxy_status_line_valid("HTTP/1.1 999 Nope")).to_be(false)
expect(reverse_proxy_status_line_valid("OK 200")).to_be(false)
```

</details>

#### should parse response header names

- Extract a response header name before filtering
   - Expected: reverse_proxy_header_name("Content-Type: text/plain") equals `Content-Type`
   - Expected: reverse_proxy_header_name("bad header") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Extract a response header name before filtering")
expect(reverse_proxy_header_name("Content-Type: text/plain")).to_equal("Content-Type")
expect(reverse_proxy_header_name("bad header")).to_equal("")
```

</details>

#### should validate upstream response header syntax

- Reject malformed upstream response headers instead of dropping them


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject malformed upstream response headers instead of dropping them")
expect(reverse_proxy_response_header_valid("Content-Type: text/plain")).to_be(true)
expect(reverse_proxy_response_header_valid("X-Trace: abc")).to_be(true)
expect(reverse_proxy_response_header_valid("bad header")).to_be(false)
expect(reverse_proxy_response_header_valid(": missing-name")).to_be(false)
```

</details>

#### should parse upstream response content length headers

- Extract declared body length for early response budget checks
   - Expected: reverse_proxy_header_value("Content-Length: 5") equals `5`
   - Expected: reverse_proxy_content_length_from_header("Content-Length: 5") equals `5`
   - Expected: reverse_proxy_content_length_from_header("content-length: 0") equals `0`
   - Expected: reverse_proxy_content_length_from_header("Content-Type: text/plain") equals `-1`
   - Expected: reverse_proxy_content_length_from_header("Content-Length: bad") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Extract declared body length for early response budget checks")
expect(reverse_proxy_header_value("Content-Length: 5")).to_equal("5")
expect(reverse_proxy_content_length_from_header("Content-Length: 5")).to_equal(5)
expect(reverse_proxy_content_length_from_header("content-length: 0")).to_equal(0)
expect(reverse_proxy_content_length_from_header("Content-Type: text/plain")).to_equal(-1)
expect(reverse_proxy_content_length_from_header("Content-Length: bad")).to_equal(-1)
```

</details>

#### should detect declared response bodies over route budget

- Reject oversized upstream responses from headers before body reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject oversized upstream responses from headers before body reads")
val route = reverse_proxy_route_with_limits("/api/", "127.0.0.1:3000", 1000, 5000, 4)
expect(reverse_proxy_declared_response_too_large("Content-Length: 5", route)).to_be(true)
expect(reverse_proxy_declared_response_too_large("Content-Length: 4", route)).to_be(false)
expect(reverse_proxy_declared_response_too_large("Content-Type: text/plain", route)).to_be(false)
```

</details>

#### should enforce upstream response header budgets

- Reject response headers that exceed configured count or line length


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject response headers that exceed configured count or line length")
val route = reverse_proxy_route_with_response_limits(
    "/api/",
    "127.0.0.1:3000",
    1000,
    5000,
    2,
    16,
    4096
)
expect(reverse_proxy_response_header_allowed("Content-Type: ok", route, 1)).to_be(true)
expect(reverse_proxy_response_header_allowed("X-Long-Header: too-long", route, 1)).to_be(false)
expect(reverse_proxy_response_header_allowed("X: ok", route, 3)).to_be(false)
```

</details>

#### should rewrite requests for close-delimited upstream forwarding

- Serialize a safe GET request for the backend process
- [


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Serialize a safe GET request for the backend process")
val route = reverse_proxy_route("/api/", "127.0.0.1:3000")
val req = proxy_req(
    HttpMethod.Get,
    "/api/users",
    "page=1",
    [("Host", "public.example"), ("Connection", "keep-alive"), ("Accept", "application/json")]
)
val wire = reverse_proxy_serialize_request(req, route)
expect(wire).to_start_with("GET /api/users?page=1 HTTP/1.1\r\n")
expect(wire).to_contain("Host: 127.0.0.1:3000\r\n")
expect(wire).to_contain("Connection: close\r\n")
expect(wire).to_contain("X-Forwarded-For: 10.0.0.7\r\n")
expect(wire).to_contain("Accept: application/json\r\n")
expect(wire.contains("public.example")).to_be(false)
expect(wire.contains("keep-alive")).to_be(false)
```

</details>

#### should forward parsed request bodies with recomputed content length

- Serialize a POST body for the backend process
- [


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Serialize a POST body for the backend process")
val route = reverse_proxy_route("/api/", "127.0.0.1:3000")
val req = proxy_req_with_body(
    HttpMethod.Post,
    "/api/users",
    "",
    [("Content-Length", "999"), ("Content-Type", "application/json")],
    "{\"name\":\"Ada\"}"
)
val wire = reverse_proxy_serialize_request(req, route)
expect(wire).to_start_with("POST /api/users HTTP/1.1\r\n")
expect(wire).to_contain("Content-Length: 14\r\n")
expect(wire).to_contain("Content-Type: application/json\r\n")
expect(wire).to_end_with("\r\n\r\n{\"name\":\"Ada\"}")
expect(wire.contains("999")).to_be(false)
```

</details>

#### should allow bounded fixed request bodies without streaming

- Keep small parsed request bodies on the buffered compatibility path
- [


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep small parsed request bodies on the buffered compatibility path")
val route = reverse_proxy_route_with_request_limits(
    "/api/",
    "127.0.0.1:3000",
    1000,
    5000,
    16,
    4096
)
val req = proxy_req_with_body(
    HttpMethod.Post,
    "/api/upload",
    "",
    [("Content-Type", "text/plain")],
    "small-body"
)
expect(reverse_proxy_request_body_streaming_required(req, route)).to_be(false)
```

</details>

#### should stream oversized fixed request bodies in bounded chunks

- Write headers separately and split fixed body bytes for upstream sends
- [
   - Expected: reverse_proxy_request_body_stream_chunk_count(req, route) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write headers separately and split fixed body bytes for upstream sends")
val route = reverse_proxy_route_with_request_limits(
    "/api/",
    "127.0.0.1:3000",
    1000,
    5000,
    4,
    4096
)
val req = proxy_req_with_body(
    HttpMethod.Post,
    "/api/upload",
    "",
    [("Content-Type", "text/plain")],
    "large"
)
expect(reverse_proxy_request_body_streaming_required(req, route)).to_be(true)
expect(reverse_proxy_request_body_streaming_supported(req, route)).to_be(true)
expect(reverse_proxy_request_body_stream_chunk_count(req, route)).to_equal(2)
val headers = reverse_proxy_serialize_request_headers(req, route)
expect(headers).to_contain("Content-Length: 5\r\n")
expect(headers).to_end_with("\r\n\r\n")
expect(headers.contains("large")).to_be(false)
```

</details>

#### should keep chunked and upgrade requests outside fixed-body streaming

- Preserve fail-closed behavior for unsupported request framing and tunnels
- [
- [


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Preserve fail-closed behavior for unsupported request framing and tunnels")
val route = reverse_proxy_route_with_request_limits(
    "/api/",
    "127.0.0.1:3000",
    1000,
    5000,
    4,
    4096
)
val chunked = proxy_req_with_body(
    HttpMethod.Post,
    "/api/upload",
    "",
    [("Transfer-Encoding", "chunked")],
    "5\r\nhello\r\n0\r\n\r\n"
)
val upgrade = proxy_req(
    HttpMethod.Get,
    "/api/ws",
    "",
    [("Connection", "Upgrade"), ("Upgrade", "websocket")]
)
expect(reverse_proxy_request_body_streaming_supported(chunked, route)).to_be(false)
expect(reverse_proxy_request_body_streaming_supported(upgrade, route)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/gpu_web_db_offload.md](doc/02_requirements/feature/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)


</details>
