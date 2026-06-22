# Dns Specification

> <details>

<!-- sdn-diagram:id=dns_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dns_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dns_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dns_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dns Specification

## Scenarios

### DNS flags encode/decode round-trip

#### encode query flags (QR=0 RD=1) gives 0x0100

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = dns_encode_flags(0, 0, 0, 0, 1, 0, 0)
expect(f).to_equal(256)
```

</details>

#### encode response flags (QR=1 RD=1 RA=1) gives 0x8180

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = dns_encode_flags(1, 0, 0, 0, 1, 1, 0)
expect(f).to_equal(33152)
```

</details>

#### decode flags round-trip QR=0 RD=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = dns_encode_flags(0, 0, 0, 0, 1, 0, 0)
val d = dns_decode_flags(f)
expect(d.0).to_equal(0)   # QR
expect(d.4).to_equal(1)   # RD
```

</details>

#### decode flags round-trip QR=1 RCODE=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = dns_encode_flags(1, 0, 0, 0, 0, 0, 3)
val d = dns_decode_flags(f)
expect(d.0).to_equal(1)   # QR
expect(d.6).to_equal(3)   # RCODE
```

</details>

### DNS wire primitive helpers

#### push_u8 appends single byte

- buf = wire push u8
   - Expected: buf.length() equals `1`
   - Expected: buf[0] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [i64] = []
buf = wire_push_u8(buf, 0x07)
expect(buf.length()).to_equal(1)
expect(buf[0]).to_equal(7)
```

</details>

#### push_u16 big-endian two bytes

- buf = wire push u16
   - Expected: buf[0] equals `0x12`
   - Expected: buf[1] equals `0x34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [i64] = []
buf = wire_push_u16(buf, 0x1234)
expect(buf[0]).to_equal(0x12)
expect(buf[1]).to_equal(0x34)
```

</details>

#### push_u32 big-endian four bytes

- buf = wire push u32
   - Expected: buf[0] equals `0`
   - Expected: buf[1] equals `0`
   - Expected: buf[2] equals `23`
   - Expected: buf[3] equals `112`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [i64] = []
buf = wire_push_u32(buf, 0x00001770)
expect(buf[0]).to_equal(0)
expect(buf[1]).to_equal(0)
expect(buf[2]).to_equal(23)
expect(buf[3]).to_equal(112)
```

</details>

#### read_u16 at offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x00, 0x01, 0x12, 0x34]
expect(wire_read_u16(bytes, 2)).to_equal(0x1234)
```

</details>

#### read_u32 at offset zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x00, 0x00, 0x17, 0x70]
expect(wire_read_u32(bytes, 0)).to_equal(6000)
```

</details>

### DNS name label encoding

#### example.com encodes to correct byte sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = wire_encode_name_to_bytes("example.com")
# \x07 e x a m p l e \x03 c o m \x00
expect(b.length()).to_equal(13)
expect(b[0]).to_equal(7)       # len("example")
expect(b[1]).to_equal(101)     # 'e'
expect(b[2]).to_equal(120)     # 'x'
expect(b[3]).to_equal(97)      # 'a'
expect(b[4]).to_equal(109)     # 'm'
expect(b[5]).to_equal(112)     # 'p'
expect(b[6]).to_equal(108)     # 'l'
expect(b[7]).to_equal(101)     # 'e'
expect(b[8]).to_equal(3)       # len("com")
expect(b[9]).to_equal(99)      # 'c'
expect(b[10]).to_equal(111)    # 'o'
expect(b[11]).to_equal(109)    # 'm'
expect(b[12]).to_equal(0)      # root label
```

</details>

#### www.example.com encodes correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = wire_encode_name_to_bytes("www.example.com")
# \x03 w w w \x07 e x a m p l e \x03 c o m \x00
# 1+3 + 1+7 + 1+3 + 1 = 17 bytes
expect(b.length()).to_equal(17)
expect(b[0]).to_equal(3)   # len("www")
expect(b[4]).to_equal(7)   # len("example")
```

</details>

#### single-label 'localhost' encodes 11 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = wire_encode_name_to_bytes("localhost")
expect(b.length()).to_equal(11)
expect(b[0]).to_equal(9)
expect(b[10]).to_equal(0)
```

</details>

### DNS query encoder — full RFC 1035 wire bytes

#### example.com A query id=0x1234 is 29 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q.length()).to_equal(29)
```

</details>

#### header bytes id=0x1234

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[0]).to_equal(0x12)
expect(q[1]).to_equal(0x34)
```

</details>

#### flags byte RD=1 gives 0x01 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[2]).to_equal(0x01)
expect(q[3]).to_equal(0x00)
```

</details>

#### QDCOUNT=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[4]).to_equal(0)
expect(q[5]).to_equal(1)
```

</details>

#### ANCOUNT NSCOUNT ARCOUNT all zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[6]).to_equal(0)
expect(q[7]).to_equal(0)
expect(q[8]).to_equal(0)
expect(q[9]).to_equal(0)
expect(q[10]).to_equal(0)
expect(q[11]).to_equal(0)
```

</details>

#### first label byte at offset 12 is 7 (len of 'example')

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[12]).to_equal(7)
```

</details>

#### label 'example' bytes are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[13]).to_equal(101)   # 'e'
expect(q[19]).to_equal(101)   # 'e' (last char of 'example')
```

</details>

#### 'com' label at offset 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[20]).to_equal(3)     # len("com")
expect(q[21]).to_equal(99)    # 'c'
expect(q[22]).to_equal(111)   # 'o'
expect(q[23]).to_equal(109)   # 'm'
expect(q[24]).to_equal(0)     # root
```

</details>

#### QTYPE=A (1) at offset 25–26

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[25]).to_equal(0)
expect(q[26]).to_equal(1)
```

</details>

#### QCLASS=IN (1) at offset 27–28

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0x1234, "example.com", DNS_TYPE_A)
expect(q[27]).to_equal(0)
expect(q[28]).to_equal(1)
```

</details>

#### AAAA query has QTYPE=28

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(1, "example.com", DNS_TYPE_AAAA)
# QTYPE at last two bytes before end
val last = q.length() - 1
expect(q[last]).to_equal(28)
expect(q[last - 1]).to_equal(0)
```

</details>

### DNS name decode with 0xC0 pointer

#### pointer C0 0C at offset 0 follows to offset 12

- 0,0,0,0, 0,0,0,0, 0,0,  # 10 pad bytes
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u16
- resp = wire push u16
- resp = wire push u8
- resp = wire push u8
- resp = wire push u16
- resp = wire push u16
- resp = wire push u32
- resp = wire push u16
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
   - Expected: answers.length() equals `1`
   - Expected: rr_name equals `a.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Byte stream: [C0 0C ...12 bytes of padding... 07 'e''x''a''m''p''l''e' 03 'c''o''m' 00]
# pointer at 0 -> offset 12 -> "example.com"
var bytes: [i64] = [0xC0, 0x0C,   # pointer -> offset 12
                    0,0,0,0, 0,0,0,0, 0,0,  # 10 pad bytes (offsets 2-11)
                    7, 101,120,97,109,112,108,101,  # \x07 example
                    3, 99,111,109,   # \x03 com
                    0]              # root
# dns_wire_decode_message needs 12-byte header first; build minimal:
# Use wire_encode_name_to_bytes directly to test pointer decode via message decode
# Instead exercise via a hand-crafted response
# Build a response: header + question + answer with C0 0C pointer
# Header: id=1 flags=0x8180 QD=1 AN=1 NS=0 AR=0
var resp: [i64] = [0x00, 0x01,  # id
                   0x81, 0x80,  # flags: QR=1 RD=1 RA=1
                   0x00, 0x01,  # QDCOUNT=1
                   0x00, 0x01,  # ANCOUNT=1
                   0x00, 0x00,  # NSCOUNT=0
                   0x00, 0x00]  # ARCOUNT=0
# Question: "a.com" A IN
resp = wire_push_u8(resp, 1)    # len("a")
resp = wire_push_u8(resp, 97)   # 'a'
resp = wire_push_u8(resp, 3)    # len("com")
resp = wire_push_u8(resp, 99)   # 'c'
resp = wire_push_u8(resp, 111)  # 'o'
resp = wire_push_u8(resp, 109)  # 'm'
resp = wire_push_u8(resp, 0)    # root
resp = wire_push_u16(resp, 1)   # QTYPE A
resp = wire_push_u16(resp, 1)   # QCLASS IN
# Answer: name via pointer C0 0C (-> offset 12 = question name)
resp = wire_push_u8(resp, 0xC0)
resp = wire_push_u8(resp, 0x0C)
resp = wire_push_u16(resp, 1)           # TYPE A
resp = wire_push_u16(resp, 1)           # CLASS IN
resp = wire_push_u32(resp, 300)         # TTL 300
resp = wire_push_u16(resp, 4)           # RDLENGTH 4
resp = wire_push_u8(resp, 93)
resp = wire_push_u8(resp, 184)
resp = wire_push_u8(resp, 216)
resp = wire_push_u8(resp, 34)           # 93.184.216.34

val msg = dns_wire_decode_message(resp)
val answers = msg.2
expect(answers.length()).to_equal(1)
# answer rr string: "a.com:1:1:300:93.184.216.34"
val rr = answers[0]
# Name part before first ':' should be "a.com"
val colon = rr.index_of(":")
val rr_name = rr.substring(0, colon)
expect(rr_name).to_equal("a.com")
```

</details>

#### A record rdata decoded as dotted-decimal IP

- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u16
- resp = wire push u16
- resp = wire push u32
- resp = wire push u16
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
- resp = wire push u8
   - Expected: rr.ends_with("1.2.3.4") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Minimal response: 1 answer, A record, ip=1.2.3.4
var resp: [i64] = [0x00, 0x02, 0x81, 0x80,
                   0x00, 0x00,  # QD=0
                   0x00, 0x01,  # AN=1
                   0x00, 0x00, 0x00, 0x00]
# Answer name: "b.com"
resp = wire_push_u8(resp, 1)
resp = wire_push_u8(resp, 98)   # 'b'
resp = wire_push_u8(resp, 3)
resp = wire_push_u8(resp, 99)   # 'c'
resp = wire_push_u8(resp, 111)  # 'o'
resp = wire_push_u8(resp, 109)  # 'm'
resp = wire_push_u8(resp, 0)
resp = wire_push_u16(resp, 1)   # A
resp = wire_push_u16(resp, 1)   # IN
resp = wire_push_u32(resp, 60)  # TTL
resp = wire_push_u16(resp, 4)   # RDLEN
resp = wire_push_u8(resp, 1)
resp = wire_push_u8(resp, 2)
resp = wire_push_u8(resp, 3)
resp = wire_push_u8(resp, 4)

val msg = dns_wire_decode_message(resp)
val answers = msg.2
val rr = answers[0]
expect(rr.ends_with("1.2.3.4")).to_equal(true)
```

</details>

### DNS message decode — question section

#### question name and type extracted from query bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0xABCD, "example.com", DNS_TYPE_A)
val msg = dns_wire_decode_message(q)
val questions = msg.1
expect(questions.length()).to_equal(1)
val q0 = questions[0]
# format: "example.com:1:1"
expect(q0.starts_with("example.com:")).to_equal(true)
```

</details>

#### decoded message header has correct id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = dns_wire_encode_query(0xABCD, "example.com", DNS_TYPE_A)
val msg = dns_wire_decode_message(q)
val header = msg.0
val id = dns_get_wire_header_id(header)
expect(id).to_equal(0xABCD)
```

</details>

### DNS type/class string helpers

#### DNS_TYPE_A is 'A'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_type_to_string(DNS_TYPE_A)).to_equal("A")
```

</details>

#### DNS_TYPE_AAAA is 'AAAA'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_type_to_string(DNS_TYPE_AAAA)).to_equal("AAAA")
```

</details>

#### DNS_TYPE_MX is 'MX'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_type_to_string(DNS_TYPE_MX)).to_equal("MX")
```

</details>

#### DNS_TYPE_CNAME is 'CNAME'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_type_to_string(DNS_TYPE_CNAME)).to_equal("CNAME")
```

</details>

#### DNS_TYPE_TXT is 'TXT'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_type_to_string(DNS_TYPE_TXT)).to_equal("TXT")
```

</details>

#### DNS_TYPE_NS is 'NS'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_type_to_string(DNS_TYPE_NS)).to_equal("NS")
```

</details>

#### DNS_CLASS_IN is 'IN'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_class_to_string(DNS_CLASS_IN)).to_equal("IN")
```

</details>

#### unknown type returns UNKNOWN

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dns_type_to_string(99)).to_equal("UNKNOWN")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/dns/dns_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DNS flags encode/decode round-trip
- DNS wire primitive helpers
- DNS name label encoding
- DNS query encoder — full RFC 1035 wire bytes
- DNS name decode with 0xC0 pointer
- DNS message decode — question section
- DNS type/class string helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
