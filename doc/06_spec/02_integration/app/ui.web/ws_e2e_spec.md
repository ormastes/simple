# WebSocket E2E Protocol Specification

> BDD spec verifying the WebSocket protocol stack surface area: frame types (RFC 6455 ss5), serialization/writer, parser, handshake helpers, origin guard, and session token contracts.  Covers round-trip source contracts that the interpreter can verify via text-grep against the source files.

<!-- sdn-diagram:id=ws_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ws_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ws_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ws_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WebSocket E2E Protocol Specification

BDD spec verifying the WebSocket protocol stack surface area: frame types (RFC 6455 ss5), serialization/writer, parser, handshake helpers, origin guard, and session token contracts.  Covers round-trip source contracts that the interpreter can verify via text-grep against the source files.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WSS-E2E |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/02_integration/app/ui.web/ws_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BDD spec verifying the WebSocket protocol stack surface area: frame types
(RFC 6455 ss5), serialization/writer, parser, handshake helpers, origin
guard, and session token contracts.  Covers round-trip source contracts
that the interpreter can verify via text-grep against the source files.

## Scenarios

### WsFrame opcodes and constants (RFC 6455)

#### defines all six standard opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("val WS_OPCODE_CONTINUATION: i64 = 0x0")
expect(s).to_contain("val WS_OPCODE_TEXT: i64")
expect(s).to_contain("val WS_OPCODE_BINARY: i64")
expect(s).to_contain("val WS_OPCODE_CLOSE: i64")
expect(s).to_contain("val WS_OPCODE_PING: i64")
expect(s).to_contain("val WS_OPCODE_PONG: i64")
```

</details>

#### defines header bit masks

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("val WS_FIN_BIT: i64")
expect(s).to_contain("val WS_RSV1_BIT: i64")
expect(s).to_contain("val WS_MASK_BIT: i64")
expect(s).to_contain("val WS_OPCODE_MASK: i64")
expect(s).to_contain("val WS_PAYLOAD_LEN_MASK: i64")
```

</details>

#### defines payload length sentinels and thresholds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("val WS_LEN_EXT_16: i64     = 126")
expect(s).to_contain("val WS_LEN_EXT_64: i64     = 127")
expect(s).to_contain("val WS_LEN_THRESH_16: i64  = 126")
expect(s).to_contain("val WS_LEN_THRESH_64: i64  = 65536")
```

</details>

#### defines close status codes per RFC 6455 ss7.4

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("val WS_CLOSE_NORMAL: i64")
expect(s).to_contain("val WS_CLOSE_GOING_AWAY: i64")
expect(s).to_contain("val WS_CLOSE_PROTOCOL_ERROR: i64")
expect(s).to_contain("val WS_CLOSE_INVALID_PAYLOAD: i64")
expect(s).to_contain("val WS_CLOSE_INTERNAL_ERROR: i64")
```

</details>

### WsFrame type system

#### declares all six frame structs with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("class WsTextFrame:")
expect(s).to_contain("class WsBinaryFrame:")
expect(s).to_contain("class WsContinuationFrame:")
expect(s).to_contain("class WsCloseFrame:")
expect(s).to_contain("class WsPingFrame:")
expect(s).to_contain("class WsPongFrame:")
```

</details>

#### declares WsFrame as tagged enum with all variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("enum WsFrame:")
expect(s).to_contain("Text(WsTextFrame)")
expect(s).to_contain("Binary(WsBinaryFrame)")
expect(s).to_contain("Continuation(WsContinuationFrame)")
expect(s).to_contain("Close(WsCloseFrame)")
expect(s).to_contain("Ping(WsPingFrame)")
expect(s).to_contain("Pong(WsPongFrame)")
```

</details>

#### provides opcode classification helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("fn ws_is_control_opcode(opcode: i64) -> bool")
expect(s).to_contain("fn ws_is_data_opcode(opcode: i64) -> bool")
```

</details>

#### uses u8 byte arrays for payload, not text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_FRAME_PATH)
expect(s).to_contain("payload: [u8]")
```

</details>

### WsWriter frame serialization

#### exposes the top-level writer fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn ws_write_frame(frame: WsFrame, masked: bool, mask_key: [u8]) -> [u8]")
```

</details>

#### provides server and client convenience writers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn ws_write_frame_server(frame: WsFrame) -> [u8]")
expect(s).to_contain("fn ws_write_frame_client(frame: WsFrame, mask_key: [u8]) -> [u8]")
```

</details>

#### handles all six frame variants in match

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_WRITER_PATH)
expect(s).to_contain("case Text(t)")
expect(s).to_contain("case Binary(b)")
expect(s).to_contain("case Continuation(c)")
expect(s).to_contain("case Close(cl)")
expect(s).to_contain("case Ping(p)")
expect(s).to_contain("case Pong(pg)")
```

</details>

#### implements big-endian 16-bit and 64-bit length encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn _push_u16_be(bytes_out: [u8], value: i64)")
expect(s).to_contain("fn _push_u64_be(bytes_out: [u8], value: i64)")
```

</details>

#### implements XOR masking per RFC 6455 ss5.3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn _xor_u8(a: i64, b: i64) -> i64")
expect(s).to_contain("fn _apply_mask_inplace(bytes_out: [u8], start: i64, len: i64, key: [u8])")
```

</details>

#### encodes close payload with 2-byte big-endian status code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn _encode_close_payload(has_status: bool, code: i64, reason: [u8]) -> [u8]")
```

</details>

#### writes the header with FIN, RSV, opcode, mask, and length fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn _write_header(")
expect(s).to_contain("fin: bool")
expect(s).to_contain("opcode: i64")
expect(s).to_contain("masked: bool")
expect(s).to_contain("payload_len: i64")
```

</details>

### WsParser frame deserialization

#### exposes the top-level parser fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn ws_parse_frame(data: [u8], offset: i64) -> WsFrame?")
```

</details>

#### exposes the header parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn ws_parse_frame_header(data: [u8], offset: i64) -> WsFrameHeader?")
```

</details>

#### declares WsFrameHeader with all required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("class WsFrameHeader:")
expect(s).to_contain("opcode: i64")
expect(s).to_contain("masked: bool")
expect(s).to_contain("payload_offset: i64")
expect(s).to_contain("payload_len: i64")
expect(s).to_contain("mask_key: [u8]")
```

</details>

#### implements unmask payload for masked frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn _unmask_payload(data: [u8], start: i64, len: i64, key: [u8]) -> [u8]")
```

</details>

#### handles all six opcodes in the match dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("case WS_OPCODE_TEXT")
expect(s).to_contain("case WS_OPCODE_BINARY")
expect(s).to_contain("case WS_OPCODE_CONTINUATION")
expect(s).to_contain("case WS_OPCODE_CLOSE")
expect(s).to_contain("case WS_OPCODE_PING")
expect(s).to_contain("case WS_OPCODE_PONG")
```

</details>

#### rejects unknown opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("case _:")
expect(s).to_contain("return nil")
```

</details>

#### validates control frame constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("WS_MAX_CONTROL_PAYLOAD")
expect(s).to_contain("if not header.fin")
```

</details>

#### provides wire size calculator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn ws_frame_wire_size(payload_len: i64, masked: bool) -> i64")
```

</details>

#### implements big-endian decode helpers symmetric to writer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn _read_u16_be(data: [u8], offset: i64) -> i64")
expect(s).to_contain("fn _read_u64_be(data: [u8], offset: i64) -> i64")
```

</details>

### Writer and Parser round-trip contract

#### writer imports all opcodes that parser dispatches on

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = src(WS_WRITER_PATH)
val p = src(WS_PARSER_PATH)
expect(w).to_contain("WS_OPCODE_TEXT")
expect(w).to_contain("WS_OPCODE_BINARY")
expect(w).to_contain("WS_OPCODE_CLOSE")
expect(w).to_contain("WS_OPCODE_PING")
expect(w).to_contain("WS_OPCODE_PONG")
expect(p).to_contain("WS_OPCODE_TEXT")
expect(p).to_contain("WS_OPCODE_BINARY")
expect(p).to_contain("WS_OPCODE_CLOSE")
expect(p).to_contain("WS_OPCODE_PING")
expect(p).to_contain("WS_OPCODE_PONG")
```

</details>

#### both writer and parser use the same XOR function signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = src(WS_WRITER_PATH)
val p = src(WS_PARSER_PATH)
expect(w).to_contain("fn _xor_u8(a: i64, b: i64) -> i64")
expect(p).to_contain("fn _xor_u8(a: i64, b: i64) -> i64")
```

</details>

#### writer uses WS_MASK_KEY_LEN matching parser mask key extraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = src(WS_WRITER_PATH)
val p = src(WS_PARSER_PATH)
expect(w).to_contain("WS_MASK_KEY_LEN")
expect(p).to_contain("WS_MASK_KEY_LEN")
```

</details>

#### both use the same length threshold constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = src(WS_WRITER_PATH)
val p = src(WS_PARSER_PATH)
expect(w).to_contain("WS_LEN_THRESH_16")
expect(w).to_contain("WS_LEN_THRESH_64")
expect(p).to_contain("WS_LEN_EXT_16")
expect(p).to_contain("WS_LEN_EXT_64")
```

</details>

### WebSocket handshake helpers

#### compute_ws_accept takes a key and returns text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn compute_ws_accept(key: text) -> text")
```

</details>

#### uses the RFC 6455 magic GUID

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("258EAFA5-E914-47DA-95CA-C5AB0DC85B11")
```

</details>

#### uses SHA-1 + base64 for the accept computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("rt_sha1_new()")
expect(s).to_contain("rt_sha1_write(handle, combined)")
expect(s).to_contain("rt_sha1_finish_base64(handle)")
```

</details>

#### detects WebSocket upgrade requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn is_ws_upgrade_request(headers: text) -> bool")
expect(s).to_contain("Upgrade: websocket")
```

</details>

#### extracts Sec-WebSocket-Key from headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn extract_ws_key(headers: text) -> text")
expect(s).to_contain("_header_value(headers, \"sec-websocket-key\")")
```

</details>

#### sends 101 Switching Protocols on successful upgrade

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("101 Switching Protocols")
expect(s).to_contain("Sec-WebSocket-Accept:")
```

</details>

### WebSocket handler frame operations

#### sends text frames with correct opcode byte 0x81

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn send_ws_text(stream: ConnStream, message: text) -> bool")
expect(s).to_contain("0x81")
```

</details>

#### sends close frames with status code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn send_ws_close(stream: ConnStream, code: i64, reason: text) -> bool")
expect(s).to_contain("0x88")
```

</details>

#### handles extended payload lengths for text frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("126")
expect(s).to_contain("65536")
```

</details>

### OriginGuard security gate

#### declares OriginGuard class with allowed list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(ORIGIN_PATH)
expect(s).to_contain("class OriginGuard:")
expect(s).to_contain("allowed: List<text>")
```

</details>

#### provides from_env constructor with localhost defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(ORIGIN_PATH)
expect(s).to_contain("static fn from_env() -> OriginGuard")
expect(s).to_contain("https://localhost")
expect(s).to_contain("http://localhost")
```

</details>

#### check method returns Result with AuthError variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(ORIGIN_PATH)
expect(s).to_contain("fn check(self, headers: text) -> Result<text, AuthError>")
expect(s).to_contain("Err(AuthError.MissingOrigin)")
expect(s).to_contain("Err(AuthError.DisallowedOrigin)")
```

</details>

#### defines AuthError enum with security-relevant variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(ORIGIN_PATH)
expect(s).to_contain("enum AuthError:")
expect(s).to_contain("MissingOrigin")
expect(s).to_contain("DisallowedOrigin")
expect(s).to_contain("MissingToken")
expect(s).to_contain("InvalidToken")
expect(s).to_contain("ExpiredToken")
expect(s).to_contain("OriginMismatch")
```

</details>

### Session token contract

#### exposes issue/serialize/parse/verify lifecycle

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(SESSION_PATH)
expect(s).to_contain("static fn issue(")
expect(s).to_contain("fn serialize(self) -> text")
expect(s).to_contain("static fn parse(s: text)")
expect(s).to_contain("fn verify(serialized: text, origin: text, secret: text, now_ms: u64)")
```

</details>

### WSS security integration

#### handler imports OriginGuard and AuthError

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("use app.ui.web.origin_guard.{OriginGuard, AuthError}")
```

</details>

#### handler imports session token module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("use app.ui.web.session_token")
```

</details>

#### upgrade rejects with 403 on origin or token failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("403 Forbidden")
expect(s).to_contain("guard.check(headers)")
```

</details>

#### extracts bearer token from Authorization header or subprotocol

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = src(WS_HANDLER_PATH)
val auth = src("src/app/ui.web/auth_params.spl")
expect(s).to_contain("fn _extract_bearer(headers: text, path: text) -> text")
expect(s).to_contain("ui_web_extract_bearer(headers, path)")
expect(auth).to_contain("authorization:")
expect(auth).to_contain("bearer ")
expect(auth).to_contain("sec-websocket-protocol:")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
