# ws_frame_round_trip_spec

> Byte-exact round-trip tests for the WebSocket framing layer (RFC 6455 §5). For each frame variant + length variant + masking direction:

<!-- sdn-diagram:id=ws_frame_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ws_frame_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ws_frame_round_trip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ws_frame_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ws_frame_round_trip_spec

Byte-exact round-trip tests for the WebSocket framing layer (RFC 6455 §5). For each frame variant + length variant + masking direction:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WS-FRAME-001 |
| Category | Stdlib / WebSocket |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/http/ws/ws_frame_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Byte-exact round-trip tests for the WebSocket framing layer (RFC 6455 §5).
For each frame variant + length variant + masking direction:

  1. Construct WsFrame value
  2. Serialize -> bytes1
  3. Parse bytes1 -> reconstructed frame
  4. Re-serialize -> bytes2
  5. Assert bytes1 == bytes2 (byte-exact stability)
  6. Assert key fields survive the round trip

Length variants exercised:
  - 7-bit  (payload <= 125)        — short text
  - 16-bit (126 .. 65535)          — medium binary
  - 64-bit (>= 65536)              — long binary

Direction variants:
  - server → client (unmasked)
  - client → server (masked, with caller-supplied 4-byte key)

Frame variants:
  - Text, Binary, Continuation, Close, Ping, Pong

Per the "text-only API byte cliffs" feedback (`feedback_text_only_byte_cliffs`)
all payload fields are [u8]. Text frames carry raw UTF-8 bytes — UTF-8
validation is a separate (caller-side) concern.

## Scenarios

### WS Text frame round-trip — 7-bit length (RFC 6455 §5.6)

#### round-trips a 5-byte 'hello' text frame byte-exact

1. payload:  short text payload
   - Expected: bytes1.len() equals `7`
   - Expected: bytes1[0] equals `0x81`
   - Expected: bytes1[1] equals `0x05`
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = WsFrame.Text(WsTextFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: _short_text_payload()
))
val bytes1 = ws_write_frame_server(original)
# 2-byte header + 5-byte payload, no mask, no ext-len
expect(bytes1.len()).to_equal(7)
# Byte 0: FIN | TEXT(0x1) = 0x81
expect(bytes1[0]).to_equal(0x81)
# Byte 1: MASK=0 | len=5
expect(bytes1[1]).to_equal(0x05)
val maybe_parsed = ws_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = ws_write_frame_server(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### preserves text payload bytes across the round trip

1. payload:  short text payload
   - Expected: t.fin is true
   - Expected: _bytes_eq(t.payload, _short_text_payload()) is true
   - Expected: "wrong-variant" equals `Text`
   - Expected: "nil-parse" equals `Some(Text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = WsFrame.Text(WsTextFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: _short_text_payload()
))
val bytes = ws_write_frame_server(original)
val maybe_parsed = ws_parse_frame(bytes, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case Text(t):
                expect(t.fin).to_equal(true)
                expect(_bytes_eq(t.payload, _short_text_payload())).to_equal(true)
            case _:
                expect("wrong-variant").to_equal("Text")
    case _:
        expect("nil-parse").to_equal("Some(Text)")
```

</details>

### WS Binary frame round-trip — 16-bit extended length

#### round-trips a 200-byte binary frame with 16-bit ext length

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _bytes_of_len(200, 0)
val original = WsFrame.Binary(WsBinaryFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: payload
))
val bytes1 = ws_write_frame_server(original)
# 2-byte header + 2-byte ext-len + 200 payload = 204
expect(bytes1.len()).to_equal(204)
# Byte 0: FIN | BINARY(0x2) = 0x82
expect(bytes1[0]).to_equal(0x82)
# Byte 1: MASK=0 | len-marker=126
expect(bytes1[1]).to_equal(WS_LEN_EXT_16)
# Bytes 2-3: big-endian 200 = 0x00 0xc8
expect(bytes1[2]).to_equal(0x00)
expect(bytes1[3]).to_equal(0xc8)
val maybe_parsed = ws_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = ws_write_frame_server(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### round-trips at 16-bit boundary (exactly 65535 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _bytes_of_len(65535, 7)
val original = WsFrame.Binary(WsBinaryFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: payload
))
val bytes1 = ws_write_frame_server(original)
# 2 + 2 + 65535
expect(bytes1.len()).to_equal(65539)
expect(bytes1[1]).to_equal(WS_LEN_EXT_16)
expect(bytes1[2]).to_equal(0xff)
expect(bytes1[3]).to_equal(0xff)
val maybe_parsed = ws_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = ws_write_frame_server(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

### WS Binary frame round-trip — 64-bit extended length

#### round-trips a 65536-byte binary frame with 64-bit ext length

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _bytes_of_len(65536, 13)
val original = WsFrame.Binary(WsBinaryFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: payload
))
val bytes1 = ws_write_frame_server(original)
# 2-byte header + 8-byte ext-len + 65536 payload = 65546
expect(bytes1.len()).to_equal(65546)
# Byte 1: MASK=0 | len-marker=127
expect(bytes1[1]).to_equal(WS_LEN_EXT_64)
# Bytes 2-9: big-endian 65536 = 0x00 0x00 0x00 0x00 0x00 0x01 0x00 0x00
expect(bytes1[2]).to_equal(0x00)
expect(bytes1[3]).to_equal(0x00)
expect(bytes1[4]).to_equal(0x00)
expect(bytes1[5]).to_equal(0x00)
expect(bytes1[6]).to_equal(0x00)
expect(bytes1[7]).to_equal(0x01)
expect(bytes1[8]).to_equal(0x00)
expect(bytes1[9]).to_equal(0x00)
val maybe_parsed = ws_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = ws_write_frame_server(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

### WS masked client → server frame (RFC 6455 §5.3)

#### round-trips a masked Text frame byte-exact

1. payload:  short text payload
   - Expected: bytes1.len() equals `11`
   - Expected: bytes1[1] equals `0x85`
   - Expected: bytes1[2] equals `0x01`
   - Expected: bytes1[3] equals `0x02`
   - Expected: bytes1[4] equals `0x03`
   - Expected: bytes1[5] equals `0x04`
   - Expected: bytes1[6] equals `0x69`
   - Expected: bytes1[7] equals `0x67`
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _mask_key_abcd()
val original = WsFrame.Text(WsTextFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: _short_text_payload()
))
val bytes1 = ws_write_frame_client(original, key)
# 2-byte header + 4-byte mask + 5-byte payload = 11
expect(bytes1.len()).to_equal(11)
# Byte 1: MASK=1 | len=5 → 0x85
expect(bytes1[1]).to_equal(0x85)
# Bytes 2-5: masking key
expect(bytes1[2]).to_equal(0x01)
expect(bytes1[3]).to_equal(0x02)
expect(bytes1[4]).to_equal(0x03)
expect(bytes1[5]).to_equal(0x04)
# Payload bytes on the wire MUST be XORed with the key —
# 'h' (0x68) XOR 0x01 = 0x69, 'e' (0x65) XOR 0x02 = 0x67, ...
expect(bytes1[6]).to_equal(0x69)
expect(bytes1[7]).to_equal(0x67)
# Round-trip stability
val maybe_parsed = ws_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
# Re-serialize with the SAME mask to compare bytes byte-exact.
val bytes2 = ws_write_frame_client(parsed, key)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### parser unmasks payload back to original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _mask_key_abcd()
val original_payload = _short_text_payload()
val original = WsFrame.Text(WsTextFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: original_payload
))
val bytes = ws_write_frame_client(original, key)
val maybe_parsed = ws_parse_frame(bytes, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case Text(t):
                # Parsed payload is the UNMASKED application bytes.
                expect(_bytes_eq(t.payload, original_payload)).to_equal(true)
            case _:
                expect("wrong-variant").to_equal("Text")
    case _:
        expect("nil-parse").to_equal("Some(Text)")
```

</details>

#### exposes mask state via the parsed frame header

1. payload:  bytes of len
   - Expected: h.masked is true
   - Expected: h.opcode equals `WS_OPCODE_BINARY`
   - Expected: h.payload_len equals `10`
   - Expected: h.mask_key.len() equals `WS_MASK_KEY_LEN`
   - Expected: "nil-header" equals `Some(header)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = _mask_key_abcd()
val original = WsFrame.Binary(WsBinaryFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: _bytes_of_len(10, 0)
))
val bytes = ws_write_frame_client(original, key)
val maybe_header = ws_parse_frame_header(bytes, 0)
match maybe_header:
    case Some(h):
        expect(h.masked).to_equal(true)
        expect(h.opcode).to_equal(WS_OPCODE_BINARY)
        expect(h.payload_len).to_equal(10)
        expect(h.mask_key.len()).to_equal(WS_MASK_KEY_LEN)
    case _:
        expect("nil-header").to_equal("Some(header)")
```

</details>

### WS Ping/Pong control frames

#### round-trips an empty Ping byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = WsFrame.Ping(WsPingFrame(fin: true, payload: _empty_bytes()))
val bytes1 = ws_write_frame_server(original)
# 2-byte header, zero payload
expect(bytes1.len()).to_equal(2)
# FIN | PING(0x9) = 0x89
expect(bytes1[0]).to_equal(0x89)
expect(bytes1[1]).to_equal(0x00)
val maybe_parsed = ws_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = ws_write_frame_server(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### round-trips a Pong with the same payload as the Ping

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ping_payload = _short_text_payload()
val ping = WsFrame.Ping(WsPingFrame(fin: true, payload: ping_payload))
val pong = WsFrame.Pong(WsPongFrame(fin: true, payload: ping_payload))
val ping_bytes = ws_write_frame_server(ping)
val pong_bytes = ws_write_frame_server(pong)
# Headers differ in opcode only.
expect(ping_bytes[0]).to_equal(0x89)
expect(pong_bytes[0]).to_equal(0x8a)
# Payloads match.
var i = 2
loop:
    if i >= ping_bytes.len():
        break
    expect(ping_bytes[i]).to_equal(pong_bytes[i])
    i = i + 1
```

</details>

#### rejects control frames with > 125 byte payload

1. wire push
2. wire push
3. wire push
4. wire push
5. wire push
   - Expected: maybe == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a malformed Ping wire by hand: opcode=0x9, 16-bit ext len 200.
var wire: [u8] = []
wire.push(0x89)            # FIN | PING
wire.push(WS_LEN_EXT_16)   # 16-bit ext marker
wire.push(0x00)
wire.push(0xc8)            # 200 big-endian
var pad = 0
loop:
    if pad >= 200:
        break
    wire.push(0x00)
    pad = pad + 1
# Per RFC 6455 §5.5: control frame payload MUST be <= 125. Parser
# surfaces this as nil so the connection layer can fail with 1002.
val maybe = ws_parse_frame(wire, 0)
expect(maybe == nil).to_equal(true)
```

</details>

### WS Close frame — status code + reason (RFC 6455 §5.5.1)

#### round-trips Close(1000, 'bye') byte-exact

1. reason push
2. reason push
3. reason push
   - Expected: bytes1.len() equals `7`
   - Expected: bytes1[0] equals `0x88`
   - Expected: bytes1[1] equals `0x05`
   - Expected: bytes1[2] equals `0x03`
   - Expected: bytes1[3] equals `0xe8`
   - Expected: bytes1[4] equals `0x62`
   - Expected: bytes1[5] equals `0x79`
   - Expected: bytes1[6] equals `0x65`
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reason: [u8] = []
reason.push(0x62)  # b
reason.push(0x79)  # y
reason.push(0x65)  # e
val original = WsFrame.Close(WsCloseFrame(
    fin: true, has_status: true,
    code: WS_CLOSE_NORMAL, reason: reason
))
val bytes1 = ws_write_frame_server(original)
# 2-byte header + 2-byte code + 3-byte reason = 7
expect(bytes1.len()).to_equal(7)
# FIN | CLOSE(0x8) = 0x88
expect(bytes1[0]).to_equal(0x88)
expect(bytes1[1]).to_equal(0x05)
# Bytes 2-3: 1000 big-endian = 0x03 0xe8
expect(bytes1[2]).to_equal(0x03)
expect(bytes1[3]).to_equal(0xe8)
# Bytes 4-6: 'bye'
expect(bytes1[4]).to_equal(0x62)
expect(bytes1[5]).to_equal(0x79)
expect(bytes1[6]).to_equal(0x65)
val maybe_parsed = ws_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = ws_write_frame_server(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### preserves Close code + reason bytes across the round trip

1. reason push
2. reason push
   - Expected: c.has_status is true
   - Expected: c.code equals `WS_CLOSE_GOING_AWAY`
   - Expected: c.reason.len() equals `2`
   - Expected: c.reason[0] equals `0x67`
   - Expected: c.reason[1] equals `0x6f`
   - Expected: "wrong-variant" equals `Close`
   - Expected: "nil-parse" equals `Some(Close)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reason: [u8] = []
reason.push(0x67)  # g
reason.push(0x6f)  # o
val original = WsFrame.Close(WsCloseFrame(
    fin: true, has_status: true,
    code: WS_CLOSE_GOING_AWAY, reason: reason
))
val bytes = ws_write_frame_server(original)
val maybe_parsed = ws_parse_frame(bytes, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case Close(c):
                expect(c.has_status).to_equal(true)
                expect(c.code).to_equal(WS_CLOSE_GOING_AWAY)
                expect(c.reason.len()).to_equal(2)
                expect(c.reason[0]).to_equal(0x67)
                expect(c.reason[1]).to_equal(0x6f)
            case _:
                expect("wrong-variant").to_equal("Close")
    case _:
        expect("nil-parse").to_equal("Some(Close)")
```

</details>

#### round-trips an empty Close payload as has_status=false

1. fin: true, has status: false, code: 0, reason:  empty bytes
   - Expected: bytes1.len() equals `2`
   - Expected: bytes1[0] equals `0x88`
   - Expected: bytes1[1] equals `0x00`
   - Expected: c.has_status is false
   - Expected: c.code equals `0`
   - Expected: "wrong-variant" equals `Close`
   - Expected: "nil-parse" equals `Some(Close)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = WsFrame.Close(WsCloseFrame(
    fin: true, has_status: false, code: 0, reason: _empty_bytes()
))
val bytes1 = ws_write_frame_server(original)
# 2-byte header, zero payload
expect(bytes1.len()).to_equal(2)
expect(bytes1[0]).to_equal(0x88)
expect(bytes1[1]).to_equal(0x00)
val maybe_parsed = ws_parse_frame(bytes1, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case Close(c):
                expect(c.has_status).to_equal(false)
                expect(c.code).to_equal(0)
            case _:
                expect("wrong-variant").to_equal("Close")
    case _:
        expect("nil-parse").to_equal("Some(Close)")
```

</details>

### WS Continuation frame round-trip (RFC 6455 §5.4)

#### round-trips a non-final Continuation byte-exact

1. payload:  short text payload
2. payload:  short text payload
   - Expected: bytes1[0] equals `0x01`
   - Expected: bytes2[0] equals `0x80`
   - Expected: maybe_a != nil is true
   - Expected: maybe_b != nil is true
   - Expected: _bytes_eq(bytes1, ws_write_frame_server(parsed_a)) is true
   - Expected: _bytes_eq(bytes2, ws_write_frame_server(parsed_b)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First fragment: Text with FIN=0
val first = WsFrame.Text(WsTextFrame(
    fin: false, rsv1: false, rsv2: false, rsv3: false,
    payload: _short_text_payload()
))
# Second fragment: Continuation with FIN=1
val second = WsFrame.Continuation(WsContinuationFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false,
    payload: _short_text_payload()
))
val bytes1 = ws_write_frame_server(first)
# FIN=0 | TEXT(0x1) = 0x01
expect(bytes1[0]).to_equal(0x01)
val bytes2 = ws_write_frame_server(second)
# FIN=1 | CONT(0x0) = 0x80
expect(bytes2[0]).to_equal(0x80)
# Round-trip stability for both
val maybe_a = ws_parse_frame(bytes1, 0)
expect(maybe_a != nil).to_equal(true)
val maybe_b = ws_parse_frame(bytes2, 0)
expect(maybe_b != nil).to_equal(true)
val parsed_a = maybe_a ?? first
val parsed_b = maybe_b ?? second
expect(_bytes_eq(bytes1, ws_write_frame_server(parsed_a))).to_equal(true)
expect(_bytes_eq(bytes2, ws_write_frame_server(parsed_b))).to_equal(true)
```

</details>

### WS wire-size predictor matches serializer output

#### predicts 7-bit wire size correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ws_frame_wire_size(5, false)).to_equal(7)
expect(ws_frame_wire_size(5, true)).to_equal(11)
```

</details>

#### predicts 16-bit wire size correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ws_frame_wire_size(200, false)).to_equal(204)
expect(ws_frame_wire_size(200, true)).to_equal(208)
```

</details>

#### predicts 64-bit wire size correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ws_frame_wire_size(65536, false)).to_equal(65546)
expect(ws_frame_wire_size(65536, true)).to_equal(65550)
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


</details>
