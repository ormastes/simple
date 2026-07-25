# Tls12 Record Handshake Round Trip Specification

> 1. fail

<!-- sdn-diagram:id=tls12_record_handshake_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tls12_record_handshake_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tls12_record_handshake_round_trip_spec -> std
tls12_record_handshake_round_trip_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tls12_record_handshake_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls12 Record Handshake Round Trip Specification

## Scenarios

### TLS 1.2 record layer round-trip

#### round-trips a handshake-content record byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frag = _fixture_handshake_payload()
val rec = make_plaintext_record(CT_HANDSHAKE, frag)
val wire = encode_record(rec)
# 5-byte header + 5-byte fragment = 10 bytes total
expect(wire.len().to_i64()).to_equal(10)
# Header byte order: type / version_major / version_minor / len_hi / len_lo
expect(rt_bytes_u8_at(wire, 0)).to_equal(CT_HANDSHAKE.to_i64())
expect(rt_bytes_u8_at(wire, 1)).to_equal(TLS12_VERSION_MAJOR.to_i64())
expect(rt_bytes_u8_at(wire, 2)).to_equal(TLS12_VERSION_MINOR.to_i64())
expect(rt_bytes_u8_at(wire, 3)).to_equal(0i64)
expect(rt_bytes_u8_at(wire, 4)).to_equal(5i64)
if val RecordResult.Ok(decoded) = decode_record(wire):
    expect(decoded.content_type).to_equal(CT_HANDSHAKE)
    expect(decoded.version_major).to_equal(TLS12_VERSION_MAJOR)
    expect(decoded.version_minor).to_equal(TLS12_VERSION_MINOR)
    expect(_bytes_equal(decoded.fragment, frag)).to_equal(true)
    # Re-encode must be byte-exact identical to wire bytes.
    val rewire = encode_record(decoded)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

#### round-trips an alert record byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frag = _fixture_alert_payload()
val rec = make_plaintext_record(CT_ALERT, frag)
val wire = encode_record(rec)
expect(rt_bytes_u8_at(wire, 0)).to_equal(CT_ALERT.to_i64())
expect(wire.len().to_i64()).to_equal(7)   # 5 header + 2 fragment
if val RecordResult.Ok(decoded) = decode_record(wire):
    expect(decoded.content_type).to_equal(CT_ALERT)
    expect(_bytes_equal(decoded.fragment, frag)).to_equal(true)
    val rewire = encode_record(decoded)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

#### round-trips an application_data record byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frag = _fixture_appdata_payload()
val rec = make_plaintext_record(CT_APPLICATION_DATA, frag)
val wire = encode_record(rec)
expect(rt_bytes_u8_at(wire, 0)).to_equal(CT_APPLICATION_DATA.to_i64())
expect(wire.len().to_i64()).to_equal(10)  # 5 header + 5 fragment
if val RecordResult.Ok(decoded) = decode_record(wire):
    expect(decoded.content_type).to_equal(CT_APPLICATION_DATA)
    expect(_bytes_equal(decoded.fragment, frag)).to_equal(true)
    val rewire = encode_record(decoded)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

#### rejects a record with truncated header

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build via _bv() — `[u8]` literal bytes decode as zero through
# rt_bytes_u8_at under the interpreter (see fixture-block comment).
val short = _bv([0x16i64, 0x03i64, 0x03i64])
if val RecordResult.Err(reason) = decode_record(short):
    expect(reason.contains("decode_error")).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

#### rejects a record whose declared length overruns the buffer

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Header says len=10 but we only supply 4 fragment bytes.
val truncated = _bv([
    0x16i64, 0x03i64, 0x03i64, 0x00i64, 0x0Ai64,
    0x00i64, 0x01i64, 0x02i64, 0x03i64
])
if val RecordResult.Err(reason) = decode_record(truncated):
    expect(reason.contains("decode_error")).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

### TLS 1.2 ClientHello round-trip

#### encodes a ClientHello with two cipher suites and no extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = _fixture_ch_no_exts()
val wire = build_client_hello(ch)
# Envelope: type(1) + uint24 length(3) = 4 bytes header.
expect(wire[0]).to_equal(HS12_CLIENT_HELLO)
# Body length: version(2) + random(32) + sid_len(1) + sid(8) +
#              cs_len(2) + cs(4) + cm_len(1) + cm(1) = 51
expect(wire[1]).to_equal(0u8)
expect(wire[2]).to_equal(0u8)
expect(wire[3]).to_equal(51u8)
expect(wire.len().to_i64()).to_equal(4 + 51)
```

</details>

#### round-trips ClientHello body byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = _fixture_ch_no_exts()
val body = build_client_hello_body(ch)
if val ClientHelloResult.Ok(parsed) = parse_client_hello(body):
    expect(parsed.client_version_major).to_equal(3u8)
    expect(parsed.client_version_minor).to_equal(3u8)
    expect(parsed.random.len().to_i64()).to_equal(32)
    expect(_bytes_equal(parsed.random, ch.random)).to_equal(true)
    expect(_bytes_equal(parsed.session_id, ch.session_id)).to_equal(true)
    expect(parsed.cipher_suites.len().to_i64()).to_equal(2)
    expect(parsed.cipher_suites[0]).to_equal(0xC02Fu16)
    expect(parsed.cipher_suites[1]).to_equal(0xC030u16)
    expect(parsed.compression_methods.len().to_i64()).to_equal(1)
    expect(parsed.compression_methods[0]).to_equal(0u8)
    expect(parsed.extensions_present).to_equal(false)
    expect(parsed.extensions.len().to_i64()).to_equal(0)
    # Re-encode body must equal original bytes.
    val rebody = build_client_hello_body(parsed)
    expect(_bytes_equal(rebody, body)).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

#### round-trips full ClientHello via the handshake envelope

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch = _fixture_ch_no_exts()
val wire = build_client_hello(ch)
if val HandshakeResult.Ok(env) = decode_handshake(wire):
    expect(env.msg_type).to_equal(HS12_CLIENT_HELLO)
    if val ClientHelloResult.Ok(parsed) = parse_client_hello(env.body):
        val rewire = build_client_hello(parsed)
        expect(_bytes_equal(rewire, wire)).to_equal(true)
    else:
        fail("unexpected TLS parse or round-trip branch")
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

### TLS 1.2 ServerHello round-trip

#### round-trips ServerHello body byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _fixture_sh_no_exts()
val body = build_server_hello_body(sh)
# Body length: version(2) + random(32) + sid_len(1) + sid(8) +
#              cipher_suite(2) + compression(1) = 46
expect(body.len().to_i64()).to_equal(46)
if val ServerHelloResult.Ok(parsed) = parse_server_hello(body):
    expect(parsed.server_version_major).to_equal(3u8)
    expect(parsed.server_version_minor).to_equal(3u8)
    expect(_bytes_equal(parsed.random, sh.random)).to_equal(true)
    expect(_bytes_equal(parsed.session_id, sh.session_id)).to_equal(true)
    expect(parsed.cipher_suite).to_equal(0xC02Fu16)
    expect(parsed.compression_method).to_equal(0u8)
    expect(parsed.extensions_present).to_equal(false)
    val rebody = build_server_hello_body(parsed)
    expect(_bytes_equal(rebody, body)).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

#### round-trips full ServerHello via the handshake envelope

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = _fixture_sh_no_exts()
val wire = build_server_hello(sh)
expect(wire[0]).to_equal(HS12_SERVER_HELLO)
if val HandshakeResult.Ok(env) = decode_handshake(wire):
    if val ServerHelloResult.Ok(parsed) = parse_server_hello(env.body):
        val rewire = build_server_hello(parsed)
        expect(_bytes_equal(rewire, wire)).to_equal(true)
    else:
        fail("unexpected TLS parse or round-trip branch")
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

### TLS 1.2 extension list round-trip

#### encodes a 2-extension list with byte-exact wire layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exts = _fixture_two_extensions()
val wire = encode_extension_list(exts)
# Outer list_len = ext1(4 + 8 = 12) + ext2(4 + 6 = 10) = 22.
expect(wire[0]).to_equal(0u8)
expect(wire[1]).to_equal(22u8)
expect(wire.len().to_i64()).to_equal(2 + 22)
# First extension: type=0x0000 (SNI), data_len=0x0008
expect(wire[2]).to_equal(0u8)
expect(wire[3]).to_equal(0u8)
expect(wire[4]).to_equal(0u8)
expect(wire[5]).to_equal(8u8)
# Second extension starts at offset 2 + 4 + 8 = 14: type=0x000A, data_len=0x0006
expect(wire[14]).to_equal(0u8)
expect(wire[15]).to_equal(10u8)
expect(wire[16]).to_equal(0u8)
expect(wire[17]).to_equal(6u8)
```

</details>

#### round-trips a 2-extension list byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exts = _fixture_two_extensions()
val wire = encode_extension_list(exts)
if val ExtensionListResult.Ok(parsed) = decode_extension_list(wire, 0u64):
    expect(parsed.len().to_i64()).to_equal(2)
    expect(parsed[0].extension_type).to_equal(EXT12_SNI)
    expect(parsed[0].extension_data.len().to_i64()).to_equal(8)
    expect(parsed[1].extension_type).to_equal(EXT12_SUPPORTED_GROUPS)
    expect(parsed[1].extension_data.len().to_i64()).to_equal(6)
    val rewire = encode_extension_list(parsed)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

#### rejects a list whose declared length truncates the last extension

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Outer says 12 bytes follow, but only 10 are present.
# Built via _bv() — interpreter `[u8]`-literal bug zero-fills via
# rt_bytes_u8_at, which would mask the negative-path check.
val bad = _bv([
    0x00i64, 0x0Ci64,
    0x00i64, 0x00i64, 0x00i64, 0x06i64, 0x00i64, 0x00i64, 0x00i64, 0x00i64, 0x00i64, 0x00i64
])
if val ExtensionListResult.Err(reason) = decode_extension_list(bad, 0u64):
    expect(reason.contains("decode_error")).to_equal(true)
else:
    fail("unexpected TLS parse or round-trip branch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls12/tls12_record_handshake_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TLS 1.2 record layer round-trip
- TLS 1.2 ClientHello round-trip
- TLS 1.2 ServerHello round-trip
- TLS 1.2 extension list round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
