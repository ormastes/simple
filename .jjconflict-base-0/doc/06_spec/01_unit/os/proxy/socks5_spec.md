# Socks5 Specification

> <details>

<!-- sdn-diagram:id=socks5_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=socks5_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

socks5_spec -> std
socks5_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=socks5_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Socks5 Specification

## Scenarios

### SOCKS5 greeting — build

#### encodes [NoAuth] as 0x05 0x01 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_greeting([Socks5Method.NoAuth])
expect(wire.len().to_i64()).to_equal(3)
expect(rt_bytes_u8_at(wire, 0)).to_equal(0x05i64)
expect(rt_bytes_u8_at(wire, 1)).to_equal(0x01i64)
expect(rt_bytes_u8_at(wire, 2)).to_equal(0x00i64)
```

</details>

#### encodes [NoAuth, UserPass] as 0x05 0x02 0x00 0x02

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_greeting([Socks5Method.NoAuth, Socks5Method.UserPass])
expect(wire.len().to_i64()).to_equal(4)
expect(rt_bytes_u8_at(wire, 0)).to_equal(0x05i64)
expect(rt_bytes_u8_at(wire, 1)).to_equal(0x02i64)
expect(rt_bytes_u8_at(wire, 2)).to_equal(0x00i64)
expect(rt_bytes_u8_at(wire, 3)).to_equal(0x02i64)
```

</details>

### SOCKS5 greeting — parse

#### parses [NoAuth] greeting

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x05i64, 0x01i64, 0x00i64])
if val GreetingResult.Ok(methods) = socks5_parse_greeting(wire):
    expect(methods.len().to_i64()).to_equal(1)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### parses [NoAuth, UserPass] greeting

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x05i64, 0x02i64, 0x00i64, 0x02i64])
if val GreetingResult.Ok(methods) = socks5_parse_greeting(wire):
    expect(methods.len().to_i64()).to_equal(2)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### rejects invalid version

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x04i64, 0x01i64, 0x00i64])
if val GreetingResult.Err(reason) = socks5_parse_greeting(wire):
    if val Socks5Error.InvalidVersion(got) = reason:
        expect(got).to_equal(0x04i64)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### rejects truncated greeting

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x05i64])
if val GreetingResult.Err(reason) = socks5_parse_greeting(wire):
    if val Socks5Error.UnexpectedEnd = reason:
        expect(reason).to_equal(Socks5Error.UnexpectedEnd)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

### SOCKS5 greeting — round-trip

#### round-trips [NoAuth] byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [Socks5Method.NoAuth]
val wire = socks5_build_greeting(methods)
if val GreetingResult.Ok(parsed) = socks5_parse_greeting(wire):
    val rewire = socks5_build_greeting(parsed)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### round-trips [NoAuth, UserPass] byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = [Socks5Method.NoAuth, Socks5Method.UserPass]
val wire = socks5_build_greeting(methods)
if val GreetingResult.Ok(parsed) = socks5_parse_greeting(wire):
    val rewire = socks5_build_greeting(parsed)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

### SOCKS5 greeting response — build

#### encodes NoAuth as 0x05 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_greeting_response(Socks5Method.NoAuth)
expect(wire.len().to_i64()).to_equal(2)
expect(rt_bytes_u8_at(wire, 0)).to_equal(0x05i64)
expect(rt_bytes_u8_at(wire, 1)).to_equal(0x00i64)
```

</details>

#### encodes NoAcceptable as 0x05 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_greeting_response(Socks5Method.NoAcceptable)
expect(wire.len().to_i64()).to_equal(2)
expect(rt_bytes_u8_at(wire, 0)).to_equal(0x05i64)
expect(rt_bytes_u8_at(wire, 1)).to_equal(0xFFi64)
```

</details>

### SOCKS5 greeting response — round-trip

#### round-trips NoAuth byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_greeting_response(Socks5Method.NoAuth)
if val GreetingResponseResult.Ok(method) = socks5_parse_greeting_response(wire):
    val rewire = socks5_build_greeting_response(method)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### round-trips NoAcceptable byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_greeting_response(Socks5Method.NoAcceptable)
if val GreetingResponseResult.Ok(method) = socks5_parse_greeting_response(wire):
    val rewire = socks5_build_greeting_response(method)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

### SOCKS5 connect request — build

#### encodes CONNECT IPv4 1.2.3.4:80 correctly

1. Socks5Atyp Ipv4
   - Expected: wire.len().to_i64() equals `10`
   - Expected: _bytes_equal(wire, expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 0x05 0x01 0x00 0x01 0x01 0x02 0x03 0x04 0x00 0x50
val wire = socks5_build_request(
    Socks5Cmd.Connect,
    Socks5Atyp.Ipv4(addr: _ipv4_1234()),
    80
)
val expected = _bv([
    0x05i64, 0x01i64, 0x00i64, 0x01i64,
    0x01i64, 0x02i64, 0x03i64, 0x04i64,
    0x00i64, 0x50i64
])
expect(wire.len().to_i64()).to_equal(10)
expect(_bytes_equal(wire, expected)).to_equal(true)
```

</details>

#### encodes CONNECT Domain 'example.com':443 correctly

1. Socks5Atyp Domain
   - Expected: wire.len().to_i64() equals `18`
   - Expected: rt_bytes_u8_at(wire, 0) equals `0x05i64`
   - Expected: rt_bytes_u8_at(wire, 1) equals `0x01i64`
   - Expected: rt_bytes_u8_at(wire, 2) equals `0x00i64`
   - Expected: rt_bytes_u8_at(wire, 3) equals `0x03i64`
   - Expected: rt_bytes_u8_at(wire, 4) equals `0x0Bi64)   # len=11`
   - Expected: rt_bytes_u8_at(wire, 5) equals `0x65i64`
   - Expected: rt_bytes_u8_at(wire, 16) equals `0x01i64`
   - Expected: rt_bytes_u8_at(wire, 17) equals `0xBBi64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 0x05 0x01 0x00 0x03 0x0B 'e'..'m' 0x01 0xBB
val wire = socks5_build_request(
    Socks5Cmd.Connect,
    Socks5Atyp.Domain(name: "example.com"),
    443
)
# 4 prefix + 1 len + 11 domain + 2 port = 18 bytes
expect(wire.len().to_i64()).to_equal(18)
expect(rt_bytes_u8_at(wire, 0)).to_equal(0x05i64)
expect(rt_bytes_u8_at(wire, 1)).to_equal(0x01i64)
expect(rt_bytes_u8_at(wire, 2)).to_equal(0x00i64)
expect(rt_bytes_u8_at(wire, 3)).to_equal(0x03i64)
expect(rt_bytes_u8_at(wire, 4)).to_equal(0x0Bi64)   # len=11
# 'e' = 0x65
expect(rt_bytes_u8_at(wire, 5)).to_equal(0x65i64)
# port 443 = 0x01 0xBB
expect(rt_bytes_u8_at(wire, 16)).to_equal(0x01i64)
expect(rt_bytes_u8_at(wire, 17)).to_equal(0xBBi64)
```

</details>

#### encodes CONNECT IPv6 ::1:80 correctly

1. Socks5Atyp Ipv6
   - Expected: wire.len().to_i64() equals `22`
   - Expected: rt_bytes_u8_at(wire, 3) equals `0x04i64)   # ATYP=IPv6`
   - Expected: rt_bytes_u8_at(wire, 19) equals `0x01i64`
   - Expected: rt_bytes_u8_at(wire, 20) equals `0x00i64`
   - Expected: rt_bytes_u8_at(wire, 21) equals `0x50i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 0x05 0x01 0x00 0x04 + 15×0x00 + 0x01 + 0x00 0x50
val wire = socks5_build_request(
    Socks5Cmd.Connect,
    Socks5Atyp.Ipv6(addr: _ipv6_loopback()),
    80
)
# 4 prefix + 16 addr + 2 port = 22 bytes
expect(wire.len().to_i64()).to_equal(22)
expect(rt_bytes_u8_at(wire, 3)).to_equal(0x04i64)   # ATYP=IPv6
# last addr byte = 0x01
expect(rt_bytes_u8_at(wire, 19)).to_equal(0x01i64)
# port 80 = 0x00 0x50
expect(rt_bytes_u8_at(wire, 20)).to_equal(0x00i64)
expect(rt_bytes_u8_at(wire, 21)).to_equal(0x50i64)
```

</details>

### SOCKS5 connect request — round-trip

#### round-trips CONNECT IPv4 byte-exact

1. Socks5Atyp Ipv4
   - Expected: _bytes_equal(rewire, wire) is true
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_request(
    Socks5Cmd.Connect,
    Socks5Atyp.Ipv4(addr: _ipv4_1234()),
    80
)
if val RequestResult.Ok(cmd, atyp, port) = socks5_parse_request(wire):
    val rewire = socks5_build_request(cmd, atyp, port)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### round-trips CONNECT Domain byte-exact

1. Socks5Atyp Domain
   - Expected: _bytes_equal(rewire, wire) is true
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_request(
    Socks5Cmd.Connect,
    Socks5Atyp.Domain(name: "example.com"),
    443
)
if val RequestResult.Ok(cmd, atyp, port) = socks5_parse_request(wire):
    val rewire = socks5_build_request(cmd, atyp, port)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### round-trips CONNECT IPv6 byte-exact

1. Socks5Atyp Ipv6
   - Expected: _bytes_equal(rewire, wire) is true
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_request(
    Socks5Cmd.Connect,
    Socks5Atyp.Ipv6(addr: _ipv6_loopback()),
    80
)
if val RequestResult.Ok(cmd, atyp, port) = socks5_parse_request(wire):
    val rewire = socks5_build_request(cmd, atyp, port)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

### SOCKS5 connect response — build

#### encodes success IPv4 0.0.0.0:0 correctly

1. Socks5Atyp Ipv4
   - Expected: wire.len().to_i64() equals `10`
   - Expected: _bytes_equal(wire, expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 0x05 0x00 0x00 0x01 0x00 0x00 0x00 0x00 0x00 0x00
val wire = socks5_build_response(
    Socks5Reply.Success,
    Socks5Atyp.Ipv4(addr: _ipv4_zeros()),
    0
)
val expected = _bv([
    0x05i64, 0x00i64, 0x00i64, 0x01i64,
    0x00i64, 0x00i64, 0x00i64, 0x00i64,
    0x00i64, 0x00i64
])
expect(wire.len().to_i64()).to_equal(10)
expect(_bytes_equal(wire, expected)).to_equal(true)
```

</details>

### SOCKS5 connect response — round-trip

#### round-trips success IPv4 byte-exact

1. Socks5Atyp Ipv4
   - Expected: _bytes_equal(rewire, wire) is true
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_response(
    Socks5Reply.Success,
    Socks5Atyp.Ipv4(addr: _ipv4_zeros()),
    0
)
if val ResponseResult.Ok(reply, atyp, port) = socks5_parse_response(wire):
    val rewire = socks5_build_response(reply, atyp, port)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### round-trips GeneralFail Domain byte-exact

1. Socks5Atyp Domain
   - Expected: _bytes_equal(rewire, wire) is true
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = socks5_build_response(
    Socks5Reply.GeneralFail,
    Socks5Atyp.Domain(name: "proxy.local"),
    0
)
if val ResponseResult.Ok(reply, atyp, port) = socks5_parse_response(wire):
    val rewire = socks5_build_response(reply, atyp, port)
    expect(_bytes_equal(rewire, wire)).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

### SOCKS5 userpass request — build

#### encodes user='user' pass='pass' correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected: 0x01 0x04 'u' 's' 'e' 'r' 0x04 'p' 'a' 's' 's'
val wire = socks5_userpass_request("user", "pass")
val expected = _bv([
    0x01i64, 0x04i64,
    0x75i64, 0x73i64, 0x65i64, 0x72i64,  # 'user'
    0x04i64,
    0x70i64, 0x61i64, 0x73i64, 0x73i64   # 'pass'
])
expect(wire.len().to_i64()).to_equal(11)
expect(_bytes_equal(wire, expected)).to_equal(true)
```

</details>

### SOCKS5 userpass response — parse

#### parses success response (0x01 0x00) as Ok(true)

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x01i64, 0x00i64])
if val UserPassResponseResult.Ok(success) = socks5_userpass_parse_response(wire):
    expect(success).to_equal(true)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### parses rejection response (0x01 0x01) as Ok(false)

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x01i64, 0x01i64])
if val UserPassResponseResult.Ok(success) = socks5_userpass_parse_response(wire):
    expect(success).to_equal(false)
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### rejects truncated userpass response

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x01i64])
if val UserPassResponseResult.Err(reason) = socks5_userpass_parse_response(wire):
    if val Socks5Error.UnexpectedEnd = reason:
        expect(reason).to_equal(Socks5Error.UnexpectedEnd)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

### SOCKS5 error cases

#### parse_request rejects invalid version

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x04i64, 0x01i64, 0x00i64, 0x01i64, 0x01i64, 0x02i64, 0x03i64, 0x04i64, 0x00i64, 0x50i64])
if val RequestResult.Err(reason) = socks5_parse_request(wire):
    if val Socks5Error.InvalidVersion(got) = reason:
        expect(got).to_equal(0x04i64)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### parse_request rejects invalid ATYP

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0x05 0x01 0x00 0x05(invalid ATYP) 0x01 0x02 0x03 0x04 0x00 0x50
val wire = _bv([0x05i64, 0x01i64, 0x00i64, 0x05i64, 0x01i64, 0x02i64, 0x03i64, 0x04i64, 0x00i64, 0x50i64])
if val RequestResult.Err(reason) = socks5_parse_request(wire):
    if val Socks5Error.InvalidAtyp(got) = reason:
        expect(got).to_equal(0x05i64)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### parse_request rejects truncated input

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x05i64, 0x01i64, 0x00i64])
if val RequestResult.Err(reason) = socks5_parse_request(wire):
    if val Socks5Error.UnexpectedEnd = reason:
        expect(reason).to_equal(Socks5Error.UnexpectedEnd)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### parse_response rejects invalid version

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x04i64, 0x00i64, 0x00i64, 0x01i64, 0x00i64, 0x00i64, 0x00i64, 0x00i64, 0x00i64, 0x00i64])
if val ResponseResult.Err(reason) = socks5_parse_response(wire):
    if val Socks5Error.InvalidVersion(got) = reason:
        expect(got).to_equal(0x04i64)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

#### parse_response rejects truncated input

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _bv([0x05i64, 0x00i64])
if val ResponseResult.Err(reason) = socks5_parse_response(wire):
    if val Socks5Error.UnexpectedEnd = reason:
        expect(reason).to_equal(Socks5Error.UnexpectedEnd)
    else:
        fail("unexpected SOCKS5 parse or framing branch")
else:
    fail("unexpected SOCKS5 parse or framing branch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/proxy/socks5_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SOCKS5 greeting — build
- SOCKS5 greeting — parse
- SOCKS5 greeting — round-trip
- SOCKS5 greeting response — build
- SOCKS5 greeting response — round-trip
- SOCKS5 connect request — build
- SOCKS5 connect request — round-trip
- SOCKS5 connect response — build
- SOCKS5 connect response — round-trip
- SOCKS5 userpass request — build
- SOCKS5 userpass response — parse
- SOCKS5 error cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
