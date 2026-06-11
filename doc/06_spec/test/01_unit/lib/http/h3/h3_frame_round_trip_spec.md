# h3_frame_round_trip_spec

> Round-trip and correctness tests for the HTTP/3 frame layer (RFC 9114 §7.2) and QPACK static table (RFC 9204 Appendix A).

<!-- sdn-diagram:id=h3_frame_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=h3_frame_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

h3_frame_round_trip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=h3_frame_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# h3_frame_round_trip_spec

Round-trip and correctness tests for the HTTP/3 frame layer (RFC 9114 §7.2) and QPACK static table (RFC 9204 Appendix A).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HTTP3-FRAME-001 |
| Category | Stdlib / HTTP/3 |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/http/h3/h3_frame_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Round-trip and correctness tests for the HTTP/3 frame layer (RFC 9114 §7.2)
and QPACK static table (RFC 9204 Appendix A).

Tests:
  - Variable-length integer encoding (RFC 9000 §16) — boundary values
  - Frame emit/parse round-trip for each frame type
  - SETTINGS payload encode/decode (empty cases)
  - QPACK static table: entry count, known-index lookups, find helpers

See test/perf/intensive/http/h3_settings_write_frame_spec.spl for the
full SETTINGS + h3_write_frame round-trip tests (require compiled mode).

## Scenarios

### H3 varint encode/decode (RFC 9000 §16)

#### encodes 0 as single byte 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = h3_varint_encode(0)
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x00)
```

</details>

#### encodes 63 as single byte 0x3f (max 1-byte)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = h3_varint_encode(63)
expect(out.len()).to_equal(1)
expect(out[0]).to_equal(0x3f)
```

</details>

#### encodes 64 as two bytes (2-byte form starts)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = h3_varint_encode(64)
expect(out.len()).to_equal(2)
# 0b01_000000 00_xxxxxx → first byte has prefix 01
expect((out[0] >> 6) & 0x03).to_equal(1)
```

</details>

#### encodes 16383 as two bytes (max 2-byte)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = h3_varint_encode(16383)
expect(out.len()).to_equal(2)
```

</details>

#### encodes 16384 as four bytes (4-byte form starts)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = h3_varint_encode(16384)
expect(out.len()).to_equal(4)
expect((out[0] >> 6) & 0x03).to_equal(2)
```

</details>

#### encodes 1073741823 as four bytes (max 4-byte)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = h3_varint_encode(1073741823)
expect(out.len()).to_equal(4)
```

</details>

#### encodes 1073741824 as eight bytes (8-byte form starts)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = h3_varint_encode(1073741824)
expect(out.len()).to_equal(8)
expect((out[0] >> 6) & 0x03).to_equal(3)
```

</details>

#### round-trips value 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = h3_varint_encode(0)
val result = h3_varint_decode(encoded, 0)
match result:
    case Ok(ok):
        expect(ok.value).to_equal(0)
        expect(ok.consumed).to_equal(1)
    case Err(_):
        expect("decode-err").to_equal("Ok")
```

</details>

#### round-trips value 37 (RFC 9000 §A.1 example)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = h3_varint_encode(37)
val result = h3_varint_decode(encoded, 0)
match result:
    case Ok(ok):
        expect(ok.value).to_equal(37)
        expect(ok.consumed).to_equal(1)
    case Err(_):
        expect("decode-err").to_equal("Ok")
```

</details>

#### round-trips value 15293 (RFC 9000 §A.1 example)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = h3_varint_encode(15293)
val result = h3_varint_decode(encoded, 0)
match result:
    case Ok(ok):
        expect(ok.value).to_equal(15293)
        expect(ok.consumed).to_equal(2)
    case Err(_):
        expect("decode-err").to_equal("Ok")
```

</details>

#### round-trips value 494878333 (RFC 9000 §A.1 example)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = h3_varint_encode(494878333)
val result = h3_varint_decode(encoded, 0)
match result:
    case Ok(ok):
        expect(ok.value).to_equal(494878333)
        expect(ok.consumed).to_equal(4)
    case Err(_):
        expect("decode-err").to_equal("Ok")
```

</details>

#### returns Err on empty buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val result = h3_varint_decode(empty, 0)
match result:
    case Err(msg):
        expect(msg).to_equal("offset past end of buffer")
    case Ok(_):
        expect("unexpected-ok").to_equal("Err")
```

</details>

#### returns Err when 2-byte varint truncated

1. buf push
   - Expected: msg equals `2-byte varint truncated`
   - Expected: "unexpected-ok" equals `Err`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
buf.push(0x40)   # prefix 01, needs 2 bytes total
val result = h3_varint_decode(buf, 0)
match result:
    case Err(msg):
        expect(msg).to_equal("2-byte varint truncated")
    case Ok(_):
        expect("unexpected-ok").to_equal("Err")
```

</details>

### H3 frame emit/parse round-trip (RFC 9114 §7.2)

#### round-trips an empty DATA frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload: [u8] = []
val wire = h3_frame_emit(H3_FRAME_DATA, payload)
val result = h3_frame_parse(wire, 0)
match result:
    case Ok(ok):
        expect(ok.frame_type).to_equal(H3_FRAME_DATA)
        expect(ok.payload.len()).to_equal(0)
        expect(ok.new_offset).to_equal(wire.len())
    case Err(_):
        expect("parse-err").to_equal("Ok")
```

</details>

#### round-trips DATA frame with 3-byte payload

1. payload push
2. payload push
3. payload push
   - Expected: ok.frame_type equals `H3_FRAME_DATA`
   - Expected: ok.payload.len() equals `3`
   - Expected: ok.payload[0] equals `0x68`
   - Expected: ok.payload[1] equals `0x69`
   - Expected: ok.payload[2] equals `0x21`
   - Expected: "parse-err" equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload: [u8] = []
payload.push(0x68)
payload.push(0x69)
payload.push(0x21)
val wire = h3_frame_emit(H3_FRAME_DATA, payload)
val result = h3_frame_parse(wire, 0)
match result:
    case Ok(ok):
        expect(ok.frame_type).to_equal(H3_FRAME_DATA)
        expect(ok.payload.len()).to_equal(3)
        expect(ok.payload[0]).to_equal(0x68)
        expect(ok.payload[1]).to_equal(0x69)
        expect(ok.payload[2]).to_equal(0x21)
    case Err(_):
        expect("parse-err").to_equal("Ok")
```

</details>

#### round-trips HEADERS frame with opaque encoded fields

1. fields push
2. fields push
3. fields push
4. fields push
   - Expected: ok.frame_type equals `H3_FRAME_HEADERS`
   - Expected: ok.payload.len() equals `4`
   - Expected: "parse-err" equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fields: [u8] = []
fields.push(0x00)
fields.push(0x00)
fields.push(0x82)
fields.push(0x86)
val wire = h3_frame_emit(H3_FRAME_HEADERS, fields)
val result = h3_frame_parse(wire, 0)
match result:
    case Ok(ok):
        expect(ok.frame_type).to_equal(H3_FRAME_HEADERS)
        expect(ok.payload.len()).to_equal(4)
    case Err(_):
        expect("parse-err").to_equal("Ok")
```

</details>

#### round-trips GOAWAY frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val goaway_payload = h3_varint_encode(100)
val wire = h3_frame_emit(H3_FRAME_GOAWAY, goaway_payload)
val result = h3_frame_parse(wire, 0)
match result:
    case Ok(ok):
        expect(ok.frame_type).to_equal(H3_FRAME_GOAWAY)
        # Decode the stream id from payload
        val id_r = h3_varint_decode(ok.payload, 0)
        match id_r:
            case Ok(id_ok):
                expect(id_ok.value).to_equal(100)
            case Err(_):
                expect("varint-err").to_equal("Ok")
    case Err(_):
        expect("parse-err").to_equal("Ok")
```

</details>

#### round-trips MAX_PUSH_ID frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val push_payload = h3_varint_encode(7)
val wire = h3_frame_emit(H3_FRAME_MAX_PUSH_ID, push_payload)
val result = h3_frame_parse(wire, 0)
match result:
    case Ok(ok):
        expect(ok.frame_type).to_equal(H3_FRAME_MAX_PUSH_ID)
        val id_r = h3_varint_decode(ok.payload, 0)
        match id_r:
            case Ok(id_ok):
                expect(id_ok.value).to_equal(7)
            case Err(_):
                expect("varint-err").to_equal("Ok")
    case Err(_):
        expect("parse-err").to_equal("Ok")
```

</details>

#### returns Err on truncated frame

1. buf push
2. buf push
   - Expected: msg equals `frame payload truncated`
   - Expected: "unexpected-ok" equals `Err`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u8] = []
buf.push(0x00)  # type = DATA
buf.push(0x05)  # length = 5 but no payload follows
val result = h3_frame_parse(buf, 0)
match result:
    case Err(msg):
        expect(msg).to_equal("frame payload truncated")
    case Ok(_):
        expect("unexpected-ok").to_equal("Err")
```

</details>

### H3 SETTINGS payload (RFC 9114 §7.2.4)

#### h3_settings_encode returns empty bytes for empty settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var settings: [H3Setting] = []
val encoded = h3_settings_encode(settings)
expect(encoded.len()).to_equal(0)
```

</details>

#### h3_settings_decode returns empty list for empty payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty: [u8] = []
val decoded = h3_settings_decode(empty)
expect(decoded.len()).to_equal(0)
```

</details>

### QPACK static table (RFC 9204 Appendix A)

#### has exactly 99 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_table_count()).to_equal(99)
```

</details>

#### entry 0 is :authority with empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_entry_0_name()).to_equal(":authority")
expect(_test_qpack_entry_0_value()).to_equal("")
```

</details>

#### entry 17 is :method GET

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_entry_17_name()).to_equal(":method")
expect(_test_qpack_entry_17_value()).to_equal("GET")
```

</details>

#### find_name returns 0 for :authority

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_find_name_authority()).to_equal(0)
```

</details>

#### find_name returns 15 for :method (first occurrence)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_find_name_method()).to_equal(15)
```

</details>

#### find_name returns -1 for unknown header

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_find_name_unknown()).to_equal(-1)
```

</details>

#### find_exact returns 17 for :method GET

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_find_exact_method_get()).to_equal(17)
```

</details>

#### find_exact returns 25 for :status 200

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_find_exact_status_200()).to_equal(25)
```

</details>

#### find_exact returns -1 for name match but wrong value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_test_qpack_find_exact_miss()).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
