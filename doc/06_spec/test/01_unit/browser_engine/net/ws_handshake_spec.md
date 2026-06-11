# Ws Handshake Specification

> 1. ws test response

<!-- sdn-diagram:id=ws_handshake_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ws_handshake_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ws_handshake_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ws_handshake_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ws Handshake Specification

## Scenarios

### WebSocket handshake response validation

#### accepts a valid 101 upgrade response

1. ws test response
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "dGhlIHNhbXBsZSBub25jZQ=="
val result = validate_handshake_response(
    ws_test_response("HTTP/1.1 101 Switching Protocols", key),
    key,
    []
)
expect(result.is_ok()).to_equal(true)
```

</details>

#### rejects non-101 status lines even when the body contains 101

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "dGhlIHNhbXBsZSBub25jZQ=="
val accept = compute_accept_key(key)
val raw = "HTTP/1.1 200 OK\r\n" +
    "Upgrade: websocket\r\n" +
    "Connection: Upgrade\r\n" +
    "Sec-WebSocket-Accept: {accept}\r\n" +
    "\r\n" +
    "body mentions 101"
val result = validate_handshake_response(raw, key, [])
expect(result.is_ok()).to_equal(false)
```

</details>

#### rejects malformed status lines with a 101 token

1. ws test response
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = "dGhlIHNhbXBsZSBub25jZQ=="
val result = validate_handshake_response(
    ws_test_response("NOTHTTP 101 Switching Protocols", key),
    key,
    []
)
expect(result.is_ok()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/net/ws_handshake_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebSocket handshake response validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
