# Websocket Facade Specification

> <details>

<!-- sdn-diagram:id=websocket_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=websocket_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

websocket_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=websocket_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Websocket Facade Specification

## Scenarios

### nogc_async_mut websocket facade

#### re-exports runtime-safe websocket helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(OPCODE_TEXT).to_equal(1)
expect(is_text_frame(OPCODE_TEXT)).to_equal(1)
expect(is_control_frame(OPCODE_CLOSE)).to_equal(1)
expect(opcode_name(OPCODE_CLOSE)).to_equal("Close")
expect(validate_frame_structure(1, OPCODE_TEXT, 5)).to_equal(1)
expect(get_header_size(125, 0)).to_equal(2)

expect(base64_encode_byte(0)).to_equal("A")
expect(base64_encode_triple(72, 105, 33)).to_equal("SGkh")

val request = build_upgrade_request("example.test", "/chat", "abc")
expect(request.contains("Upgrade: websocket")).to_equal(true)
expect(parse_upgrade_response("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n")).to_equal(1)

expect(close_status_name(CLOSE_NORMAL)).to_equal("Normal Closure")
expect(is_valid_close_status(CLOSE_NORMAL)).to_equal(1)

expect(frame_info(1, OPCODE_TEXT, 0, 2)).to_equal("Frame: FIN | Text | UNMASKED | Payload: 2 bytes")
expect(text_payload_length("Hi")).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/websocket/websocket_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut websocket facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
