# Test Api Mount Specification

> <details>

<!-- sdn-diagram:id=test_api_mount_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_api_mount_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_api_mount_spec -> std
test_api_mount_spec -> common
test_api_mount_spec -> nogc_sync_mut
test_api_mount_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_api_mount_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Api Mount Specification

## Scenarios

### test_api_mount

#### exposes the canonical route prefix

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TEST_API_PREFIX).to_equal("/api/test/")
```

</details>

#### test_api_matches returns true only for /api/test/ paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_api_matches("/api/test/ready")).to_equal(true)
expect(test_api_matches("/api/test/ui/snapshot")).to_equal(true)
expect(test_api_matches("/api/state")).to_equal(false)
expect(test_api_matches("/")).to_equal(false)
expect(test_api_matches("")).to_equal(false)
```

</details>

#### dispatch_test_api returns the ready probe against any session

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _trivial_session()
val result = dispatch_test_api(
    "/api/test/ready",
    "GET",
    "",
    session,
    \_: pass_dn
)
expect(result.0).to_equal(200)
expect(result.1).to_equal("application/json")
expect(result.2).to_contain("\"ready\":true")
expect(result.2).to_contain("\"protocol_version\":1")
```

</details>

#### dispatch_test_api surfaces a multi-mode UI snapshot

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _trivial_session()
val result = dispatch_test_api(
    "/api/test/ui/snapshot",
    "GET",
    "",
    session,
    \_: pass_dn
)
expect(result.0).to_equal(200)
expect(result.2).to_contain("\"protocol_version\":1")
```

</details>

#### format_http_response emits a well-formed HTTP/1.1 response

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = format_http_response(200, "application/json", "{\"ok\":true}")
expect(response).to_start_with("HTTP/1.1 200 OK")
expect(response).to_contain("Content-Type: application/json")
expect(response).to_contain("X-UI-Protocol-Version: 1")
expect(response).to_contain("Content-Length: 11")
expect(response).to_end_with("{\"ok\":true}")
```

</details>

#### format_http_response maps known error statuses

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val not_found = format_http_response(404, "text/plain", "nope")
expect(not_found).to_start_with("HTTP/1.1 404 Not Found")
val bad = format_http_response(400, "application/json", "{}")
expect(bad).to_start_with("HTTP/1.1 400 Bad Request")
val forbidden = format_http_response(403, "application/json", "{}")
expect(forbidden).to_start_with("HTTP/1.1 403 Forbidden")
```

</details>

#### format_http_response emits Protocol v2 only for Draw IR responses

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val draw_ir = format_http_response(200, "application/vnd.simple.draw-ir+json", "{\"protocol_version\":2}")
expect(draw_ir).to_contain("X-UI-Protocol-Version: 2")
val ready = format_http_response(200, "application/json", "{\"protocol_version\":1}")
expect(ready).to_contain("X-UI-Protocol-Version: 1")
```

</details>

#### dispatch_and_format combines dispatch + encode in one call

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _trivial_session()
val encoded = dispatch_and_format(
    "/api/test/ready",
    "GET",
    "",
    session,
    \_: pass_dn
)
expect(encoded).to_start_with("HTTP/1.1 200 OK")
expect(encoded).to_contain("\"ready\":true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/test_api_mount_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- test_api_mount

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
