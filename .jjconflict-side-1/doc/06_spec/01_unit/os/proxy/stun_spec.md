# Stun Specification

> 1. fail

<!-- sdn-diagram:id=stun_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stun_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stun_spec -> std
stun_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stun_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stun Specification

## Scenarios

### RFC 5769 §2.1 Sample Request — parse

#### parses as Binding Request class and method

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec21_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    expect(msg.class_).to_equal(StunClass.Request)
    expect(msg.method).to_equal(StunMethod.Binding)
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### decodes transaction ID byte-exact

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec21_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    val txn = msg.transaction_id
    expect(txn.len().to_i64()).to_equal(12)
    expect(rt_bytes_u8_at(txn, 0)).to_equal(0xb7i64)
    expect(rt_bytes_u8_at(txn, 1)).to_equal(0xe7i64)
    expect(rt_bytes_u8_at(txn, 2)).to_equal(0xa7i64)
    expect(rt_bytes_u8_at(txn, 3)).to_equal(0x01i64)
    expect(rt_bytes_u8_at(txn, 4)).to_equal(0xbci64)
    expect(rt_bytes_u8_at(txn, 5)).to_equal(0x34i64)
    expect(rt_bytes_u8_at(txn, 6)).to_equal(0xd6i64)
    expect(rt_bytes_u8_at(txn, 7)).to_equal(0x86i64)
    expect(rt_bytes_u8_at(txn, 8)).to_equal(0xfai64)
    expect(rt_bytes_u8_at(txn, 9)).to_equal(0x87i64)
    expect(rt_bytes_u8_at(txn, 10)).to_equal(0xdfi64)
    expect(rt_bytes_u8_at(txn, 11)).to_equal(0xaei64)
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### has 6 attributes

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [0]=SOFTWARE, [1]=PRIORITY(Unknown 0x0024),
# [2]=ICE-CONTROLLED(Unknown 0x8029), [3]=USERNAME,
# [4]=MESSAGE-INTEGRITY, [5]=FINGERPRINT(Unknown 0x8028)
val wire = _sec21_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    expect(msg.attributes.len().to_i64()).to_equal(6)
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### attr[3] is USERNAME evtj:h6vY

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec21_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.Username(value) = msg.attributes[3]:
        expect(value).to_equal("evtj:h6vY")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### attr[4] is MESSAGE-INTEGRITY with 20-byte HMAC-SHA1

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec21_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.MessageIntegrity(hmac) = msg.attributes[4]:
        expect(hmac.len().to_i64()).to_equal(20)
        expect(rt_bytes_u8_at(hmac, 0)).to_equal(0x9ai64)
        expect(rt_bytes_u8_at(hmac, 19)).to_equal(0xa2i64)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### attr[0] is SOFTWARE

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec21_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.Software(value) = msg.attributes[0]:
        expect(value).to_equal("STUN test client")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### attr[5] FINGERPRINT parses as Unknown(0x8028) with CRC32 e5 7a 3b cf

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec21_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.Unknown(type_code, value) = msg.attributes[5]:
        expect(type_code).to_equal(0x8028i64)
        expect(value.len().to_i64()).to_equal(4)
        expect(rt_bytes_u8_at(value, 0)).to_equal(0xe5i64)
        expect(rt_bytes_u8_at(value, 1)).to_equal(0x7ai64)
        expect(rt_bytes_u8_at(value, 2)).to_equal(0x3bi64)
        expect(rt_bytes_u8_at(value, 3)).to_equal(0xcfi64)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

### RFC 5769 §2.1 Sample Request — semantic round-trip

#### parse then build then reparse yields same class, method, txn_id, attr count

1. fail
2. fail
3. fail
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: byte-exact round-trip not possible — RFC 5769 uses 0x20 padding;
# stun_build emits RFC-correct 0x00 padding. Both are valid per RFC 5389.
val wire = _sec21_wire()
if val StunParseResult.Ok(msg1) = stun_parse(wire):
    val rebuilt = stun_build(msg1)
    if val StunParseResult.Ok(msg2) = stun_parse(rebuilt):
        if val StunClass.Request = msg2.class_:
            if val StunMethod.Binding = msg2.method:
                expect(msg2.attributes.len().to_i64()).to_equal(6)
                expect(_bytes_equal(msg2.transaction_id, msg1.transaction_id)).to_equal(true)
            else:
                fail("unexpected STUN parse or attribute branch")
        else:
            fail("unexpected STUN parse or attribute branch")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

### RFC 5769 §2.2 Sample IPv4 Response — parse

#### parses as Binding SuccessResp

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec22_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    expect(msg.class_).to_equal(StunClass.SuccessResp)
    expect(msg.method).to_equal(StunMethod.Binding)
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### has 4 attributes

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# [0]=SOFTWARE, [1]=XOR-MAPPED-ADDRESS,
# [2]=MESSAGE-INTEGRITY, [3]=FINGERPRINT(Unknown 0x8028)
val wire = _sec22_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    expect(msg.attributes.len().to_i64()).to_equal(4)
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### attr[0] is SOFTWARE test vector

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec22_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.Software(value) = msg.attributes[0]:
        expect(value).to_equal("test vector")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### XOR-MAPPED-ADDRESS decodes to 192.0.2.1 port 32853

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec22_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.XorMappedAddress(family, ip, port) = msg.attributes[1]:
        expect(family).to_equal(0x01i64)
        expect(port).to_equal(32853)
        expect(ip.len().to_i64()).to_equal(4)
        expect(rt_bytes_u8_at(ip, 0)).to_equal(192)
        expect(rt_bytes_u8_at(ip, 1)).to_equal(0)
        expect(rt_bytes_u8_at(ip, 2)).to_equal(2)
        expect(rt_bytes_u8_at(ip, 3)).to_equal(1)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### MESSAGE-INTEGRITY is 20 bytes with correct boundary bytes

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec22_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.MessageIntegrity(hmac) = msg.attributes[2]:
        expect(hmac.len().to_i64()).to_equal(20)
        expect(rt_bytes_u8_at(hmac, 0)).to_equal(0x2bi64)
        expect(rt_bytes_u8_at(hmac, 19)).to_equal(0xd7i64)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### FINGERPRINT is Unknown(0x8028) with bytes c0 7d 4c 96

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec22_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.Unknown(type_code, value) = msg.attributes[3]:
        expect(type_code).to_equal(0x8028i64)
        expect(rt_bytes_u8_at(value, 0)).to_equal(0xc0i64)
        expect(rt_bytes_u8_at(value, 1)).to_equal(0x7di64)
        expect(rt_bytes_u8_at(value, 2)).to_equal(0x4ci64)
        expect(rt_bytes_u8_at(value, 3)).to_equal(0x96i64)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

### RFC 5769 §2.2 Sample IPv4 Response — semantic round-trip

#### parse then build then reparse yields same class, method, txn_id, attr count

1. fail
2. fail
3. fail
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec22_wire()
if val StunParseResult.Ok(msg1) = stun_parse(wire):
    val rebuilt = stun_build(msg1)
    if val StunParseResult.Ok(msg2) = stun_parse(rebuilt):
        if val StunClass.SuccessResp = msg2.class_:
            if val StunMethod.Binding = msg2.method:
                expect(msg2.attributes.len().to_i64()).to_equal(4)
                expect(_bytes_equal(msg2.transaction_id, msg1.transaction_id)).to_equal(true)
            else:
                fail("unexpected STUN parse or attribute branch")
        else:
            fail("unexpected STUN parse or attribute branch")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### round-tripped XOR-MAPPED-ADDRESS preserves 192.0.2.1 port 32853

1. fail
2. fail
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec22_wire()
if val StunParseResult.Ok(msg1) = stun_parse(wire):
    val rebuilt = stun_build(msg1)
    if val StunParseResult.Ok(msg2) = stun_parse(rebuilt):
        if val StunAttr.XorMappedAddress(family, ip, port) = msg2.attributes[1]:
            expect(family).to_equal(0x01i64)
            expect(port).to_equal(32853)
            expect(rt_bytes_u8_at(ip, 0)).to_equal(192)
            expect(rt_bytes_u8_at(ip, 3)).to_equal(1)
        else:
            fail("unexpected STUN parse or attribute branch")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

### RFC 5769 §2.3 Sample IPv6 Response — parse

#### parses as Binding SuccessResp

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    expect(msg.class_).to_equal(StunClass.SuccessResp)
    expect(msg.method).to_equal(StunMethod.Binding)
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### has 4 attributes

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    expect(msg.attributes.len().to_i64()).to_equal(4)
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### attr[0] is SOFTWARE test vector

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.Software(value) = msg.attributes[0]:
        expect(value).to_equal("test vector")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### XOR-MAPPED-ADDRESS decodes to 2001:db8:1234:5678:11:2233:4455:6677 port 32853

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.XorMappedAddress(family, ip, port) = msg.attributes[1]:
        expect(family).to_equal(0x02i64)
        expect(port).to_equal(32853)
        expect(ip.len().to_i64()).to_equal(16)
        # 2001:0db8:1234:5678:0011:2233:4455:6677
        expect(rt_bytes_u8_at(ip, 0)).to_equal(0x20i64)
        expect(rt_bytes_u8_at(ip, 1)).to_equal(0x01i64)
        expect(rt_bytes_u8_at(ip, 2)).to_equal(0x0di64)
        expect(rt_bytes_u8_at(ip, 3)).to_equal(0xb8i64)
        expect(rt_bytes_u8_at(ip, 4)).to_equal(0x12i64)
        expect(rt_bytes_u8_at(ip, 5)).to_equal(0x34i64)
        expect(rt_bytes_u8_at(ip, 6)).to_equal(0x56i64)
        expect(rt_bytes_u8_at(ip, 7)).to_equal(0x78i64)
        expect(rt_bytes_u8_at(ip, 8)).to_equal(0x00i64)
        expect(rt_bytes_u8_at(ip, 9)).to_equal(0x11i64)
        expect(rt_bytes_u8_at(ip, 10)).to_equal(0x22i64)
        expect(rt_bytes_u8_at(ip, 11)).to_equal(0x33i64)
        expect(rt_bytes_u8_at(ip, 12)).to_equal(0x44i64)
        expect(rt_bytes_u8_at(ip, 13)).to_equal(0x55i64)
        expect(rt_bytes_u8_at(ip, 14)).to_equal(0x66i64)
        expect(rt_bytes_u8_at(ip, 15)).to_equal(0x77i64)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### MESSAGE-INTEGRITY is 20 bytes with correct boundary bytes

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.MessageIntegrity(hmac) = msg.attributes[2]:
        expect(hmac.len().to_i64()).to_equal(20)
        expect(rt_bytes_u8_at(hmac, 0)).to_equal(0xa3i64)
        expect(rt_bytes_u8_at(hmac, 19)).to_equal(0x41i64)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### FINGERPRINT is Unknown(0x8028) with bytes c8 fb 0b 4c

1. fail
2. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg) = stun_parse(wire):
    if val StunAttr.Unknown(type_code, value) = msg.attributes[3]:
        expect(type_code).to_equal(0x8028i64)
        expect(rt_bytes_u8_at(value, 0)).to_equal(0xc8i64)
        expect(rt_bytes_u8_at(value, 1)).to_equal(0xfbi64)
        expect(rt_bytes_u8_at(value, 2)).to_equal(0x0bi64)
        expect(rt_bytes_u8_at(value, 3)).to_equal(0x4ci64)
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

### RFC 5769 §2.3 Sample IPv6 Response — semantic round-trip

#### parse then build then reparse yields same class, method, txn_id, attr count

1. fail
2. fail
3. fail
4. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg1) = stun_parse(wire):
    val rebuilt = stun_build(msg1)
    if val StunParseResult.Ok(msg2) = stun_parse(rebuilt):
        if val StunClass.SuccessResp = msg2.class_:
            if val StunMethod.Binding = msg2.method:
                expect(msg2.attributes.len().to_i64()).to_equal(4)
                expect(_bytes_equal(msg2.transaction_id, msg1.transaction_id)).to_equal(true)
            else:
                fail("unexpected STUN parse or attribute branch")
        else:
            fail("unexpected STUN parse or attribute branch")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

#### round-tripped XOR-MAPPED-ADDRESS IPv6 preserves 2001:db8:: port 32853

1. fail
2. fail
3. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wire = _sec23_wire()
if val StunParseResult.Ok(msg1) = stun_parse(wire):
    val rebuilt = stun_build(msg1)
    if val StunParseResult.Ok(msg2) = stun_parse(rebuilt):
        if val StunAttr.XorMappedAddress(family, ip, port) = msg2.attributes[1]:
            expect(family).to_equal(0x02i64)
            expect(port).to_equal(32853)
            expect(ip.len().to_i64()).to_equal(16)
            expect(rt_bytes_u8_at(ip, 0)).to_equal(0x20i64)
            expect(rt_bytes_u8_at(ip, 1)).to_equal(0x01i64)
            expect(rt_bytes_u8_at(ip, 15)).to_equal(0x77i64)
        else:
            fail("unexpected STUN parse or attribute branch")
    else:
        fail("unexpected STUN parse or attribute branch")
else:
    fail("unexpected STUN parse or attribute branch")
```

</details>

### RFC 5769 wire buffer lengths

#### §2.1 wire is 108 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sec21_wire().len().to_i64()).to_equal(108)
```

</details>

#### §2.2 wire is 80 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sec22_wire().len().to_i64()).to_equal(80)
```

</details>

#### §2.3 wire is 92 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sec23_wire().len().to_i64()).to_equal(92)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/proxy/stun_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RFC 5769 §2.1 Sample Request — parse
- RFC 5769 §2.1 Sample Request — semantic round-trip
- RFC 5769 §2.2 Sample IPv4 Response — parse
- RFC 5769 §2.2 Sample IPv4 Response — semantic round-trip
- RFC 5769 §2.3 Sample IPv6 Response — parse
- RFC 5769 §2.3 Sample IPv6 Response — semantic round-trip
- RFC 5769 wire buffer lengths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
