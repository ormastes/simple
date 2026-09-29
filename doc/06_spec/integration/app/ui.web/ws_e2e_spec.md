# WebSocket E2E Protocol Specification

> BDD spec verifying the WebSocket protocol stack surface area: frame types (RFC 6455 ss5), serialization/writer, parser, handshake helpers, origin guard, and session token contracts.  Covers round-trip source contracts that the interpreter can verify via text-grep against the source files.

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
| Source | `test/integration/app/ui.web/ws_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

BDD spec verifying the WebSocket protocol stack surface area: frame types
(RFC 6455 ss5), serialization/writer, parser, handshake helpers, origin
guard, and session token contracts.  Covers round-trip source contracts
that the interpreter can verify via text-grep against the source files.

## Scenarios

### WsFrame opcodes and constants (RFC 6455)

#### defines all six standard opcodes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines all six standard opcodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines all six standard opcodes")
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

- defines header bit masks


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines header bit masks")
val s = src(WS_FRAME_PATH)
expect(s).to_contain("val WS_FIN_BIT: i64")
expect(s).to_contain("val WS_RSV1_BIT: i64")
expect(s).to_contain("val WS_MASK_BIT: i64")
expect(s).to_contain("val WS_OPCODE_MASK: i64")
expect(s).to_contain("val WS_PAYLOAD_LEN_MASK: i64")
```

</details>

#### defines payload length sentinels and thresholds

- defines payload length sentinels and thresholds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines payload length sentinels and thresholds")
val s = src(WS_FRAME_PATH)
expect(s).to_contain("val WS_LEN_EXT_16: i64     = 126")
expect(s).to_contain("val WS_LEN_EXT_64: i64     = 127")
expect(s).to_contain("val WS_LEN_THRESH_16: i64  = 126")
expect(s).to_contain("val WS_LEN_THRESH_64: i64  = 65536")
```

</details>

#### defines close status codes per RFC 6455 ss7.4

- defines close status codes per RFC 6455 ss7.4


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines close status codes per RFC 6455 ss7.4")
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

- declares all six frame structs with correct fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares all six frame structs with correct fields")
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

- declares WsFrame as tagged enum with all variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares WsFrame as tagged enum with all variants")
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

- provides opcode classification helpers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides opcode classification helpers")
val s = src(WS_FRAME_PATH)
expect(s).to_contain("fn ws_is_control_opcode(opcode: i64) -> bool")
expect(s).to_contain("fn ws_is_data_opcode(opcode: i64) -> bool")
```

</details>

#### uses u8 byte arrays for payload, not text

- uses u8 byte arrays for payload, not text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses u8 byte arrays for payload, not text")
val s = src(WS_FRAME_PATH)
expect(s).to_contain("payload: [u8]")
```

</details>

### WsWriter frame serialization

#### exposes the top-level writer fn

- exposes the top-level writer fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes the top-level writer fn")
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn ws_write_frame(frame: WsFrame, masked: bool, mask_key: [u8]) -> [u8]")
```

</details>

#### provides server and client convenience writers

- provides server and client convenience writers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides server and client convenience writers")
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn ws_write_frame_server(frame: WsFrame) -> [u8]")
expect(s).to_contain("fn ws_write_frame_client(frame: WsFrame, mask_key: [u8]) -> [u8]")
```

</details>

#### handles all six frame variants in match

- handles all six frame variants in match


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles all six frame variants in match")
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

- implements big-endian 16-bit and 64-bit length encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("implements big-endian 16-bit and 64-bit length encoding")
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn _push_u16_be(bytes_out: [u8], value: i64)")
expect(s).to_contain("fn _push_u64_be(bytes_out: [u8], value: i64)")
```

</details>

#### implements XOR masking per RFC 6455 ss5.3

- implements XOR masking per RFC 6455 ss5.3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("implements XOR masking per RFC 6455 ss5.3")
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn _xor_u8(a: i64, b: i64) -> i64")
expect(s).to_contain("fn _apply_mask_inplace(bytes_out: [u8], start: i64, len: i64, key: [u8])")
```

</details>

#### encodes close payload with 2-byte big-endian status code

- encodes close payload with 2-byte big-endian status code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("encodes close payload with 2-byte big-endian status code")
val s = src(WS_WRITER_PATH)
expect(s).to_contain("fn _encode_close_payload(has_status: bool, code: i64, reason: [u8]) -> [u8]")
```

</details>

#### writes the header with FIN, RSV, opcode, mask, and length fields

- writes the header with FIN, RSV, opcode, mask, and length fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes the header with FIN, RSV, opcode, mask, and length fields")
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

- exposes the top-level parser fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes the top-level parser fn")
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn ws_parse_frame(data: [u8], offset: i64) -> WsFrame?")
```

</details>

#### exposes the header parser

- exposes the header parser


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes the header parser")
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn ws_parse_frame_header(data: [u8], offset: i64) -> WsFrameHeader?")
```

</details>

#### declares WsFrameHeader with all required fields

- declares WsFrameHeader with all required fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares WsFrameHeader with all required fields")
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

- implements unmask payload for masked frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("implements unmask payload for masked frames")
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn _unmask_payload(data: [u8], start: i64, len: i64, key: [u8]) -> [u8]")
```

</details>

#### handles all six opcodes in the equality dispatch

- handles all six opcodes in the equality dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles all six opcodes in the equality dispatch")
val s = src(WS_PARSER_PATH)
# NOT `case WS_OPCODE_*`: WS_OPCODE_* are `val` i64 constants, so in
# `case` position a bare identifier is an IRREFUTABLE BINDING PATTERN and
# every frame dispatched as Text (lint MEXH006,
# doc/08_tracking/bug/case_bare_ident_is_irrefutable_binding_2026-08-01.md).
# ws_parser.spl:248-257 is the comment forbidding `case`, and it was the
# ONLY place the old needles matched -- the spec asserted the exact
# construct the product is required not to use.
expect(s).to_contain("if header.opcode == WS_OPCODE_TEXT:")
expect(s).to_contain("elif header.opcode == WS_OPCODE_BINARY:")
expect(s).to_contain("elif header.opcode == WS_OPCODE_CONTINUATION:")
expect(s).to_contain("elif header.opcode == WS_OPCODE_CLOSE:")
expect(s).to_contain("elif header.opcode == WS_OPCODE_PING:")
expect(s).to_contain("elif header.opcode == WS_OPCODE_PONG:")
```

</details>

#### rejects unknown opcodes

- rejects unknown opcodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unknown opcodes")
val s = src(WS_PARSER_PATH)
# Fall-through after the last equality arm, not a `case _:` catch-all.
expect(s).to_contain("return _build_pong_frame(header, payload)")
expect(s).to_contain("\n    return nil")
expect(s).to_contain("return nil")
```

</details>

#### validates control frame constraints

- validates control frame constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("validates control frame constraints")
val s = src(WS_PARSER_PATH)
expect(s).to_contain("WS_MAX_CONTROL_PAYLOAD")
expect(s).to_contain("if not header.fin")
```

</details>

#### provides wire size calculator

- provides wire size calculator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides wire size calculator")
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn ws_frame_wire_size(payload_len: i64, masked: bool) -> i64")
```

</details>

#### implements big-endian decode helpers symmetric to writer

- implements big-endian decode helpers symmetric to writer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("implements big-endian decode helpers symmetric to writer")
val s = src(WS_PARSER_PATH)
expect(s).to_contain("fn _read_u16_be(data: [u8], offset: i64) -> i64")
expect(s).to_contain("fn _read_u64_be(data: [u8], offset: i64) -> i64")
```

</details>

### Writer and Parser round-trip contract

#### writer imports all opcodes that parser dispatches on

- writer imports all opcodes that parser dispatches on


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writer imports all opcodes that parser dispatches on")
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

- both writer and parser use the same XOR function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("both writer and parser use the same XOR function signature")
val w = src(WS_WRITER_PATH)
val p = src(WS_PARSER_PATH)
expect(w).to_contain("fn _xor_u8(a: i64, b: i64) -> i64")
expect(p).to_contain("fn _xor_u8(a: i64, b: i64) -> i64")
```

</details>

#### writer uses WS_MASK_KEY_LEN matching parser mask key extraction

- writer uses WS_MASK_KEY_LEN matching parser mask key extraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writer uses WS_MASK_KEY_LEN matching parser mask key extraction")
val w = src(WS_WRITER_PATH)
val p = src(WS_PARSER_PATH)
expect(w).to_contain("WS_MASK_KEY_LEN")
expect(p).to_contain("WS_MASK_KEY_LEN")
```

</details>

#### both use the same length threshold constants

- both use the same length threshold constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("both use the same length threshold constants")
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

- compute_ws_accept takes a key and returns text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compute_ws_accept takes a key and returns text")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn compute_ws_accept(key: text) -> text")
```

</details>

#### uses the RFC 6455 magic GUID

- uses the RFC 6455 magic GUID


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses the RFC 6455 magic GUID")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("258EAFA5-E914-47DA-95CA-C5AB0DC85B11")
```

</details>

#### uses SHA-1 + base64 for the accept computation

- uses SHA-1 + base64 for the accept computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses SHA-1 + base64 for the accept computation")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("rt_sha1_new()")
expect(s).to_contain("rt_sha1_write(handle, combined)")
expect(s).to_contain("rt_sha1_finish_base64(handle)")
```

</details>

#### detects WebSocket upgrade requests

- detects WebSocket upgrade requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects WebSocket upgrade requests")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn is_ws_upgrade_request(headers: text) -> bool")
expect(s).to_contain("Upgrade: websocket")
```

</details>

#### extracts Sec-WebSocket-Key from headers

- extracts Sec-WebSocket-Key from headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts Sec-WebSocket-Key from headers")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn extract_ws_key(headers: text) -> text")
expect(s).to_contain("Sec-WebSocket-Key:")
```

</details>

#### sends 101 Switching Protocols on successful upgrade

- sends 101 Switching Protocols on successful upgrade


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sends 101 Switching Protocols on successful upgrade")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("101 Switching Protocols")
expect(s).to_contain("Sec-WebSocket-Accept:")
```

</details>

### WebSocket handler frame operations

#### sends text frames with correct opcode byte 0x81

- sends text frames with correct opcode byte 0x81


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sends text frames with correct opcode byte 0x81")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn send_ws_text(stream: ConnStream, message: text) -> bool")
expect(s).to_contain("0x81")
```

</details>

#### sends close frames with status code

- sends close frames with status code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sends close frames with status code")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn send_ws_close(stream: ConnStream, code: i64, reason: text) -> bool")
expect(s).to_contain("0x88")
```

</details>

#### handles extended payload lengths for text frames

- handles extended payload lengths for text frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles extended payload lengths for text frames")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("126")
expect(s).to_contain("65536")
```

</details>

### OriginGuard security gate

#### declares OriginGuard class with allowed list

- declares OriginGuard class with allowed list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares OriginGuard class with allowed list")
val s = src(ORIGIN_PATH)
expect(s).to_contain("class OriginGuard:")
expect(s).to_contain("allowed: List<text>")
```

</details>

#### provides from_env constructor with localhost defaults

- provides from_env constructor with localhost defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides from_env constructor with localhost defaults")
val s = src(ORIGIN_PATH)
expect(s).to_contain("static fn from_env() -> OriginGuard")
expect(s).to_contain("https://localhost")
expect(s).to_contain("http://localhost")
```

</details>

#### check method returns Result with AuthError variants

- check method returns Result with AuthError variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("check method returns Result with AuthError variants")
val s = src(ORIGIN_PATH)
expect(s).to_contain("fn check(self, headers: text) -> Result<text, AuthError>")
expect(s).to_contain("Err(AuthError.MissingOrigin)")
expect(s).to_contain("Err(AuthError.DisallowedOrigin)")
```

</details>

#### defines AuthError enum with security-relevant variants

- defines AuthError enum with security-relevant variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines AuthError enum with security-relevant variants")
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

- exposes issue/serialize/parse/verify lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes issue/serialize/parse/verify lifecycle")
val s = src(SESSION_PATH)
expect(s).to_contain("static fn issue(")
expect(s).to_contain("fn serialize(self) -> text")
expect(s).to_contain("static fn parse(s: text)")
expect(s).to_contain("fn verify(serialized: text, origin: text, secret: text, now_ms: u64)")
```

</details>

### WSS security integration

#### handler imports OriginGuard and AuthError

- handler imports OriginGuard and AuthError


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handler imports OriginGuard and AuthError")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("use app.ui.web.origin_guard.{OriginGuard, AuthError}")
```

</details>

#### handler imports session token module

- handler imports session token module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handler imports session token module")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("use app.ui.web.session_token")
```

</details>

#### upgrade rejects with 403 on origin or token failure

- upgrade rejects with 403 on origin or token failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("upgrade rejects with 403 on origin or token failure")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("403 Forbidden")
expect(s).to_contain("guard.check(headers)")
```

</details>

#### extracts bearer token from Authorization header or query param

- extracts bearer token from Authorization header or query param


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts bearer token from Authorization header or query param")
val s = src(WS_HANDLER_PATH)
expect(s).to_contain("fn _extract_bearer(headers: text, path: text) -> text")
expect(s).to_contain("authorization:")
expect(s).to_contain("bearer ")
expect(s).to_contain("?token=")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2633646e4e03b0c2af4d2dec2307479ada3d320ecd1158ee33ac4cf717d7a402`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2633646e4e03b0c2af4d2dec2307479ada3d320ecd1158ee33ac4cf717d7a402`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2633646e4e03b0c2af4d2dec2307479ada3d320ecd1158ee33ac4cf717d7a402`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/ui.web/ws_e2e_spec.spl
mirror: doc/06_spec/integration/app/ui.web/ws_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/ui.web/ws_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/ui.web/ws_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/ui.web/ws_e2e_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines all six standard opcodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/ui.web/ws_e2e_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines header bit masks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/ui.web/ws_e2e_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines payload length sentinels and thresholds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
