# h2_frame_round_trip_spec

> Byte-exact round-trip tests for the H2 framing layer (RFC 9113 §4 + §6). Each frame type: 1. Construct H2Frame value 2. Serialize -> bytes1 3. Parse bytes1 -> reconstructed frame 4. Re-serialize -> bytes2 5. Assert bytes1 == bytes2 (byte-exact stability) 6. Assert key fields match across the round-trip

<!-- sdn-diagram:id=h2_frame_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=h2_frame_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

h2_frame_round_trip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=h2_frame_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# h2_frame_round_trip_spec

Byte-exact round-trip tests for the H2 framing layer (RFC 9113 §4 + §6). Each frame type: 1. Construct H2Frame value 2. Serialize -> bytes1 3. Parse bytes1 -> reconstructed frame 4. Re-serialize -> bytes2 5. Assert bytes1 == bytes2 (byte-exact stability) 6. Assert key fields match across the round-trip

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HTTP2-FRAME-001 |
| Category | Stdlib / HTTP/2 |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/http/h2/h2_frame_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Byte-exact round-trip tests for the H2 framing layer (RFC 9113 §4 + §6).
Each frame type:
  1. Construct H2Frame value
  2. Serialize -> bytes1
  3. Parse bytes1 -> reconstructed frame
  4. Re-serialize -> bytes2
  5. Assert bytes1 == bytes2 (byte-exact stability)
  6. Assert key fields match across the round-trip

Plus:
  - R-bit (reserved) parser masking — a frame whose stream_id has the top bit
    set MUST be parsed with R-bit ignored and stream_id = bottom 31 bits.
  - Connection preface 24-byte literal compare.
  - SETTINGS ACK (empty payload) and PING ACK flag combos.

Out-of-scope sanity (these MUST be parser-rejected, not silently accepted):
  - DATA on stream 0 (§6.1)
  - SETTINGS on non-zero stream id (§6.5)
  - PING with payload != 8 bytes (§6.7)
  - SETTINGS payload length not multiple of 6 (§6.5)

## Scenarios

### H2 connection preface (RFC 9113 §3.4)

#### preface bytes are exactly 24 bytes long

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = h2_connection_preface_bytes()
expect(p.len()).to_equal(24)
```

</details>

#### preface starts with 'PRI'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = h2_connection_preface_bytes()
expect(p[0]).to_equal(0x50)
expect(p[1]).to_equal(0x52)
expect(p[2]).to_equal(0x49)
```

</details>

#### preface ends with \\r\\n\\r\\n

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = h2_connection_preface_bytes()
expect(p[20]).to_equal(0x0d)
expect(p[21]).to_equal(0x0a)
expect(p[22]).to_equal(0x0d)
expect(p[23]).to_equal(0x0a)
```

</details>

#### validates a correct preface

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = h2_connection_preface_bytes()
expect(h2_validate_preface(p)).to_equal(true)
```

</details>

#### rejects a too-short buffer

1. short push
2. short push
   - Expected: h2_validate_preface(short) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var short: [u8] = []
short.push(0x50)
short.push(0x52)
expect(h2_validate_preface(short)).to_equal(false)
```

</details>

#### rejects a corrupted preface

1. var bad = h2 connection preface bytes
   - Expected: h2_validate_preface(bad) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad = h2_connection_preface_bytes()
# Corrupt one byte in the middle.
bad[10] = 0x00
expect(h2_validate_preface(bad)).to_equal(false)
```

</details>

### H2 frame header byte layout

#### writes a 9-byte header for a zero-length payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val ping_ack = H2Frame.Ping(H2PingFrame(flags: H2_FLAG_ACK, opaque_data: _opaque_eight()))
val bytes = h2_write_frame(ping_ack)
# 9 header + 8 PING payload
expect(bytes.len()).to_equal(H2_FRAME_HEADER_LEN + 8)
```

</details>

#### encodes type byte at offset 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data_frame = H2Frame.Data(H2DataFrame(stream_id: 1, flags: 0, data: _payload_three()))
val bytes = h2_write_frame(data_frame)
expect(bytes[3]).to_equal(0x0)   # H2_FRAME_DATA
```

</details>

#### encodes length big-endian in first 3 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data_frame = H2Frame.Data(H2DataFrame(stream_id: 1, flags: 0, data: _payload_three()))
val bytes = h2_write_frame(data_frame)
expect(bytes[0]).to_equal(0)
expect(bytes[1]).to_equal(0)
expect(bytes[2]).to_equal(3)
```

</details>

#### always writes R-bit as 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# stream_id with top bit set in i64 — writer must mask it before
# emitting the 31-bit field.
val data_frame = H2Frame.Data(H2DataFrame(stream_id: 0xffffffff, flags: 0, data: _payload_three()))
val bytes = h2_write_frame(data_frame)
# byte 5 is the high byte of the 32-bit stream-id word; top bit MUST be 0.
val top_bit = bytes[5] & 0x80
expect(top_bit).to_equal(0)
```

</details>

### H2 DATA frame round-trip (RFC 9113 §6.1)

#### round-trips DATA(stream_id=1, END_STREAM, payload='hi!') byte-exact

1. data:  payload three
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = H2Frame.Data(H2DataFrame(
    stream_id: 1,
    flags: H2_FLAG_END_STREAM,
    data: _payload_three()
))
val bytes1 = h2_write_frame(original)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? H2Frame.Data(H2DataFrame(stream_id: 0, flags: 0, data: []))
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### preserves flags and payload across parse

1. data:  payload three
   - Expected: d.stream_id equals `7`
   - Expected: d.flags equals `H2_FLAG_END_STREAM`
   - Expected: d.data.len() equals `3`
   - Expected: d.data[0] equals `0x68`
   - Expected: "wrong-variant" equals `Data`
   - Expected: "nil-parse" equals `Some(Data)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = H2Frame.Data(H2DataFrame(
    stream_id: 7,
    flags: H2_FLAG_END_STREAM,
    data: _payload_three()
))
val bytes1 = h2_write_frame(original)
val maybe_parsed = h2_parse_frame(bytes1, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case Data(d):
                expect(d.stream_id).to_equal(7)
                expect(d.flags).to_equal(H2_FLAG_END_STREAM)
                expect(d.data.len()).to_equal(3)
                expect(d.data[0]).to_equal(0x68)
            case _:
                expect("wrong-variant").to_equal("Data")
    case _:
        expect("nil-parse").to_equal("Some(Data)")
```

</details>

#### rejects DATA on stream 0 (RFC 9113 §6.1)

1. bytes push
2. bytes push
3. bytes push
4. bytes push
5. bytes push
6. bytes push
7. bytes push
8. bytes push
9. bytes push
10. bytes push
11. bytes push
12. bytes push
   - Expected: parsed == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Manually build a DATA frame on stream 0 and confirm parser refuses.
var bytes: [u8] = []
bytes.push(0)       # length hi
bytes.push(0)
bytes.push(3)       # length=3
bytes.push(0x0)     # type=DATA
bytes.push(0)       # flags
bytes.push(0)       # stream id all zero
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0x68)
bytes.push(0x69)
bytes.push(0x21)
val parsed = h2_parse_frame(bytes, 0)
expect(parsed == nil).to_equal(true)
```

</details>

### H2 HEADERS frame round-trip (RFC 9113 §6.2)

#### round-trips HEADERS(END_STREAM | END_HEADERS, opaque header_block) byte-exact

1. hb push
2. hb push
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Header block stays opaque — HPACK is W16+.
var hb: [u8] = []
hb.push(0x82)   # would be HPACK static-index for :method GET
hb.push(0x86)   # would be HPACK static-index for :scheme http
val original = H2Frame.Headers(H2HeadersFrame(
    stream_id: 3,
    flags: H2_FLAG_END_STREAM | H2_FLAG_END_HEADERS,
    header_block: hb
))
val bytes1 = h2_write_frame(original)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

### H2 SETTINGS frame round-trip (RFC 9113 §6.5)

#### round-trips SETTINGS with two parameters byte-exact

1. settings push
2. settings push
   - Expected: bytes1.len() equals `21`
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var settings: [H2Setting] = []
settings.push(H2Setting(identifier: H2_SETTINGS_MAX_CONCURRENT_STREAMS, value: 100))
settings.push(H2Setting(identifier: H2_SETTINGS_INITIAL_WINDOW_SIZE, value: 65535))
val original = H2Frame.Settings(H2SettingsFrame(
    flags: 0,
    settings: settings
))
val bytes1 = h2_write_frame(original)
# 9 header + 2*6 payload = 21
expect(bytes1.len()).to_equal(21)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### round-trips SETTINGS-ACK (empty payload) byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [H2Setting] = []
val ack = H2Frame.Settings(H2SettingsFrame(
    flags: H2_FLAG_ACK,
    settings: empty
))
val bytes1 = h2_write_frame(ack)
# 9 header + 0 payload
expect(bytes1.len()).to_equal(9)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? ack
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### preserves setting identifier and value across parse

1. settings push
   - Expected: s.settings.len() equals `1`
   - Expected: s.settings[0].identifier equals `H2_SETTINGS_MAX_CONCURRENT_STREAMS`
   - Expected: s.settings[0].value equals `250`
   - Expected: "wrong-variant" equals `Settings`
   - Expected: "nil-parse" equals `Some(Settings)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var settings: [H2Setting] = []
settings.push(H2Setting(identifier: H2_SETTINGS_MAX_CONCURRENT_STREAMS, value: 250))
val original = H2Frame.Settings(H2SettingsFrame(flags: 0, settings: settings))
val bytes1 = h2_write_frame(original)
val maybe_parsed = h2_parse_frame(bytes1, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case Settings(s):
                expect(s.settings.len()).to_equal(1)
                expect(s.settings[0].identifier).to_equal(H2_SETTINGS_MAX_CONCURRENT_STREAMS)
                expect(s.settings[0].value).to_equal(250)
            case _:
                expect("wrong-variant").to_equal("Settings")
    case _:
        expect("nil-parse").to_equal("Some(Settings)")
```

</details>

#### rejects SETTINGS on non-zero stream id

1. bytes push
2. bytes push
3. bytes push
4. bytes push
5. bytes push
6. bytes push
7. bytes push
8. bytes push
9. bytes push
   - Expected: parsed == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a SETTINGS frame manually with stream_id=1 — illegal per §6.5.
var bytes: [u8] = []
bytes.push(0)
bytes.push(0)
bytes.push(0)       # length=0
bytes.push(0x4)     # type=SETTINGS
bytes.push(0)       # flags
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(1)       # stream_id=1
val parsed = h2_parse_frame(bytes, 0)
expect(parsed == nil).to_equal(true)
```

</details>

#### rejects non-ACK SETTINGS with payload length not multiple of 6

1. bytes push
2. bytes push
3. bytes push
4. bytes push
5. bytes push
6. bytes push
7. bytes push
8. bytes push
9. bytes push
10. bytes push
11. bytes push
12. bytes push
13. bytes push
14. bytes push
   - Expected: parsed == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = []
bytes.push(0)
bytes.push(0)
bytes.push(5)       # length=5 (not multiple of 6)
bytes.push(0x4)     # type=SETTINGS
bytes.push(0)       # flags=0 (not ACK)
bytes.push(0)       # stream_id=0
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0)
val parsed = h2_parse_frame(bytes, 0)
expect(parsed == nil).to_equal(true)
```

</details>

### H2 PING frame round-trip (RFC 9113 §6.7)

#### round-trips PING with 8-byte opaque payload byte-exact

1. opaque data:  opaque eight
   - Expected: bytes1.len() equals `17`
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = H2Frame.Ping(H2PingFrame(
    flags: 0,
    opaque_data: _opaque_eight()
))
val bytes1 = h2_write_frame(original)
# 9 header + 8 payload
expect(bytes1.len()).to_equal(17)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### round-trips PING-ACK byte-exact

1. opaque data:  opaque eight
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ack = H2Frame.Ping(H2PingFrame(
    flags: H2_FLAG_ACK,
    opaque_data: _opaque_eight()
))
val bytes1 = h2_write_frame(ack)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? ack
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### rejects PING with payload length != 8

1. bytes push
2. bytes push
3. bytes push
4. bytes push
5. bytes push
6. bytes push
7. bytes push
8. bytes push
9. bytes push
10. bytes push
11. bytes push
12. bytes push
13. bytes push
   - Expected: parsed == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = []
bytes.push(0)
bytes.push(0)
bytes.push(4)       # length=4 (illegal, must be exactly 8)
bytes.push(0x6)     # type=PING
bytes.push(0)       # flags
bytes.push(0)       # stream_id=0
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0xaa)
bytes.push(0xbb)
bytes.push(0xcc)
bytes.push(0xdd)
val parsed = h2_parse_frame(bytes, 0)
expect(parsed == nil).to_equal(true)
```

</details>

### H2 GOAWAY frame round-trip (RFC 9113 §6.8)

#### round-trips GOAWAY with non-empty debug_data byte-exact

1. debug push
2. debug push
3. debug push
   - Expected: maybe_parsed != nil is true
   - Expected: _bytes_eq(bytes1, bytes2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var debug: [u8] = []
debug.push(0x42)
debug.push(0x55)
debug.push(0x47)   # 'B', 'U', 'G'
val original = H2Frame.Goaway(H2GoawayFrame(
    last_stream_id: 5,
    error_code: H2_ERR_PROTOCOL_ERROR,
    debug_data: debug
))
val bytes1 = h2_write_frame(original)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### round-trips GOAWAY with empty debug_data byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val original = H2Frame.Goaway(H2GoawayFrame(
    last_stream_id: 0,
    error_code: H2_ERR_NO_ERROR,
    debug_data: empty
))
val bytes1 = h2_write_frame(original)
# 9 header + 8 mandatory payload
expect(bytes1.len()).to_equal(17)
val maybe_parsed = h2_parse_frame(bytes1, 0)
expect(maybe_parsed != nil).to_equal(true)
val parsed = maybe_parsed ?? original
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### preserves last_stream_id and error_code

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val original = H2Frame.Goaway(H2GoawayFrame(
    last_stream_id: 99,
    error_code: H2_ERR_PROTOCOL_ERROR,
    debug_data: empty
))
val bytes1 = h2_write_frame(original)
val maybe_parsed = h2_parse_frame(bytes1, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case Goaway(g):
                expect(g.last_stream_id).to_equal(99)
                expect(g.error_code).to_equal(H2_ERR_PROTOCOL_ERROR)
            case _:
                expect("wrong-variant").to_equal("Goaway")
    case _:
        expect("nil-parse").to_equal("Some(Goaway)")
```

</details>

### H2 RST_STREAM and WINDOW_UPDATE round-trip (§6.4 / §6.9)

#### round-trips RST_STREAM byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = H2Frame.RstStream(H2RstStreamFrame(
    stream_id: 11,
    error_code: H2_ERR_PROTOCOL_ERROR
))
val bytes1 = h2_write_frame(original)
# 9 + 4
expect(bytes1.len()).to_equal(13)
val maybe_parsed = h2_parse_frame(bytes1, 0)
val parsed = maybe_parsed ?? original
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

#### round-trips connection-level WINDOW_UPDATE byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = H2Frame.WindowUpdate(H2WindowUpdateFrame(
    stream_id: 0,
    increment: 65535
))
val bytes1 = h2_write_frame(original)
expect(bytes1.len()).to_equal(13)
val maybe_parsed = h2_parse_frame(bytes1, 0)
val parsed = maybe_parsed ?? original
val bytes2 = h2_write_frame(parsed)
expect(_bytes_eq(bytes1, bytes2)).to_equal(true)
```

</details>

### H2 frame header R-bit masking (RFC 9113 §4.1)

#### parses stream_id ignoring R-bit set in incoming bytes

1. bytes push
2. bytes push
3. bytes push
4. bytes push
5. bytes push
6. bytes push
7. bytes push
8. bytes push
9. bytes push
10. bytes push
11. bytes push
12. bytes push
13. bytes push
   - Expected: h.stream_id equals `1)   # R masked off`
   - Expected: h.frame_type equals `0x8`
   - Expected: h.length equals `4`
   - Expected: "nil-header" equals `Some(header)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hand-craft a WINDOW_UPDATE on stream_id=1 with the R-bit set in the
# raw 32-bit stream-id word (top bit). Parser MUST mask it off.
var bytes: [u8] = []
bytes.push(0)
bytes.push(0)
bytes.push(4)        # length=4
bytes.push(0x8)      # type=WINDOW_UPDATE
bytes.push(0)        # flags
bytes.push(0x80)     # stream_id top byte with R-bit set
bytes.push(0)
bytes.push(0)
bytes.push(1)        # stream_id low = 1, full word = 0x80000001
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(10)       # increment=10
val maybe_header = h2_parse_frame_header(bytes, 0)
match maybe_header:
    case Some(h):
        expect(h.stream_id).to_equal(1)   # R masked off
        expect(h.frame_type).to_equal(0x8)
        expect(h.length).to_equal(4)
    case _:
        expect("nil-header").to_equal("Some(header)")
```

</details>

#### round-trips a WINDOW_UPDATE whose raw bytes had R-bit set

1. bytes push
2. bytes push
3. bytes push
4. bytes push
5. bytes push
6. bytes push
7. bytes push
8. bytes push
9. bytes push
10. bytes push
11. bytes push
12. bytes push
13. bytes push
   - Expected: w.stream_id equals `2`
   - Expected: w.increment equals `20`
   - Expected: top equals `0`
   - Expected: "wrong-variant" equals `WindowUpdate`
   - Expected: "nil-parse" equals `Some(WindowUpdate)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After parsing, re-serialization MUST emit R=0 (per writer) — the
# second-pass bytes will differ from the first only in the R-bit, so
# we compare stream_id field instead of byte-exact.
var bytes: [u8] = []
bytes.push(0)
bytes.push(0)
bytes.push(4)
bytes.push(0x8)
bytes.push(0)
bytes.push(0x80)     # R-bit set
bytes.push(0)
bytes.push(0)
bytes.push(2)
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(20)
val maybe_parsed = h2_parse_frame(bytes, 0)
match maybe_parsed:
    case Some(frame):
        match frame:
            case WindowUpdate(w):
                expect(w.stream_id).to_equal(2)
                expect(w.increment).to_equal(20)
                # Re-serialize and verify R-bit is now zero.
                val out = h2_write_frame(frame)
                val top = out[5] & 0x80
                expect(top).to_equal(0)
            case _:
                expect("wrong-variant").to_equal("WindowUpdate")
    case _:
        expect("nil-parse").to_equal("Some(WindowUpdate)")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
