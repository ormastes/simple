# Simple Portal Server Specification

> <details>

<!-- sdn-diagram:id=simple_portal_server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_portal_server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_portal_server_spec -> std
simple_portal_server_spec -> app
simple_portal_server_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_portal_server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Portal Server Specification

## Scenarios

### simple_portal server

#### serves the landing page from the app filesystem root

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = _server().route_request("GET", "/", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("Filesystem-first portal")
expect(resp).to_contain("Content-Security-Policy:")
```

</details>

#### normalizes duplicate slashes for public APIs

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = _server().route_request("GET", "//api//portal//releases//", "", "")
expect(resp).to_start_with("HTTP/1.1 200 OK")
expect(resp).to_contain("\"releases\"")
```

</details>

#### rejects static path traversal

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = _server().route_request("GET", "/static/../content/pages.db", "", "")
expect(resp).to_start_with("HTTP/1.1 404 Not Found")
```

</details>

#### rejects disallowed methods on public endpoints

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = _server().route_request("POST", "/api/portal/pages", "{}", "")
expect(resp).to_start_with("HTTP/1.1 405 Method Not Allowed")
expect(resp).to_contain("Allow: GET, HEAD")
```

</details>

#### rejects unauthorized playground runs

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Origin: http://localhost:4040\nX-Simple-Portal-Capability: playground.run\n"
val resp = _server().route_request("POST", "/api/playground/run", "{\"source\":\"print 1\"}", headers)
expect(resp).to_start_with("HTTP/1.1 403 Forbidden")
```

</details>

#### accepts authorized playground runs and returns a sandbox envelope

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = "Origin: http://localhost:4040\nX-Simple-Portal-Capability: playground.run\nX-Simple-Portal-Token: dev-token\n"
val resp = _server().route_request("POST", "/api/playground/run", "{\"mode\":\"sandbox\",\"source\":\"print 1\"}", headers)
expect(resp).to_start_with("HTTP/1.1 202 Accepted")
expect(resp).to_contain("\"runner\":\"simple run --sandbox\"")
expect(resp).to_contain("\"sandbox\":{\"filesystem\":false,\"network\":false,\"process\":false}")
```

</details>

#### rejects oversized playground bodies

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var body = "{"
var i = 0
while i < 17000:
    body = body + "a"
    i = i + 1
body = body + "}"
val headers = "Origin: http://localhost:4040\nX-Simple-Portal-Capability: playground.run\nX-Simple-Portal-Token: dev-token\n"
val resp = _server().route_request("POST", "/api/playground/run", body, headers)
expect(resp).to_start_with("HTTP/1.1 413 Request Entity Too Large")
```

</details>

### simple_portal app identity

#### uses stable sys app paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_portal_app_id()).to_equal("/sys/apps/simple_portal")
expect(simple_portal_exec_path()).to_equal("/sys/apps/simple_portal.smf")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/simple_portal/simple_portal_server_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple_portal server
- simple_portal app identity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
