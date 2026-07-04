# Hello Retry Request Specification

> <details>

<!-- sdn-diagram:id=hello_retry_request_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hello_retry_request_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hello_retry_request_spec -> std
hello_retry_request_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hello_retry_request_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hello Retry Request Specification

## Scenarios

### HRR magic-bytes detection

#### detects HRR when ServerHello.random == HRR_MAGIC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = ServerHello13(random: _hrr_random_bytes(), cipher_suite: 0x1301u16, x25519_pub: [], p256_pub: [])
expect(is_hello_retry_request(sh)).to_equal(true)
```

</details>

#### rejects ServerHello whose random differs by even one byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sh = ServerHello13(random: _flipped_random_bytes(), cipher_suite: 0x1301u16, x25519_pub: [], p256_pub: [])
expect(is_hello_retry_request(sh)).to_equal(false)
```

</details>

#### HRR_MAGIC is exactly 32 bytes and starts with 0xCF 0x21 0xAD 0x74

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(HRR_MAGIC.len().to_u64()).to_equal(32u64)
expect(HRR_MAGIC[0]).to_equal(0xCFu8)
expect(HRR_MAGIC[1]).to_equal(0x21u8)
expect(HRR_MAGIC[2]).to_equal(0xADu8)
expect(HRR_MAGIC[3]).to_equal(0x74u8)
```

</details>

### parse_hello_retry_request happy paths

#### extracts cipher_suite, selected_group, and cookie when all present

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_hello_retry_request(_hrr_with_cookie())
if val HrrResult.Ok(value) = res:
    expect(value.cipher_suite).to_equal(0x1301u16)
    expect(value.selected_group).to_equal(0x0017u16)
    expect(value.cookie.len().to_u64()).to_equal(4u64)
    expect(value.cookie[0]).to_equal(0xCAu8)
    expect(value.cookie[1]).to_equal(0xFEu8)
    expect(value.cookie[2]).to_equal(0xBAu8)
    expect(value.cookie[3]).to_equal(0xBEu8)
else:
    fail("unexpected TLS13 HRR parse branch")
```

</details>

#### yields empty cookie when HRR omits the cookie extension

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_hello_retry_request(_hrr_no_cookie())
if val HrrResult.Ok(value) = res:
    expect(value.selected_group).to_equal(0x0017u16)
    expect(value.cookie.len().to_u64()).to_equal(0u64)
else:
    fail("unexpected TLS13 HRR parse branch")
```

</details>

### parse_hello_retry_request rejections

#### rejects HRR with legacy_compression_method != 0x00

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_hello_retry_request(_hrr_bad_compression())
if val HrrResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
    expect(reason.contains("compression")).to_equal(true)
else:
    fail("unexpected TLS13 HRR parse branch")
```

</details>

#### rejects HRR whose supported_versions != 0x0304

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_hello_retry_request(_hrr_bad_supported_versions())
if val HrrResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
    expect(reason.contains("supported_versions")).to_equal(true)
else:
    fail("unexpected TLS13 HRR parse branch")
```

</details>

#### rejects HRR missing the key_share extension

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_hello_retry_request(_hrr_no_key_share())
if val HrrResult.Err(reason) = res:
    expect(reason.contains("missing_extension")).to_equal(true)
else:
    fail("unexpected TLS13 HRR parse branch")
```

</details>

#### rejects truncated HRR body (< 38 bytes)

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short_body: [u8] = [0x03u8, 0x03u8]
val res = parse_hello_retry_request(short_body)
if val HrrResult.Err(reason) = res:
    expect(reason.contains("decode_error")).to_equal(true)
else:
    fail("unexpected TLS13 HRR parse branch")
```

</details>

#### still parses but flags same-group HRR via selected_group field

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The wire-level parser cannot know what CH1 sent. The connect-flow
# caller is responsible for comparing parsed selected_group against
# CH1's offered group and rejecting if equal — RFC 8446 §4.1.4.
val res = parse_hello_retry_request(_hrr_same_group_x25519())
if val HrrResult.Ok(value) = res:
    expect(value.selected_group).to_equal(GROUP_X25519)
else:
    fail("unexpected TLS13 HRR parse branch")
```

</details>

### build_hrr_synthetic_message_hash byte-exact format

#### emits 0xfe 0x00 0x00 0x20 || Hash(CH1) for SHA-256 input

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ch1_hash = _ch1_hash_fixture()
val msg = build_hrr_synthetic_message_hash(ch1_hash)
expect(msg.len().to_u64()).to_equal(36u64)
expect(msg[0]).to_equal(0xFEu8)
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x20u8)
# Body bytes 4..36 must equal the input hash byte-for-byte.
var i: u64 = 0
while i < 32:
    expect(msg[4 + i]).to_equal(ch1_hash[i])
    i = i + 1
```

</details>

#### uses the message_hash handshake type 254 (0xfe)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(HS_MESSAGE_HASH).to_equal(254u8)
```

</details>

#### encodes hash length as big-endian u24 in handshake header

1. short hash push
   - Expected: msg.len().to_u64() equals `20u64`
   - Expected: msg[0] equals `0xFEu8`
   - Expected: msg[1] equals `0x00u8`
   - Expected: msg[2] equals `0x00u8`
   - Expected: msg[3] equals `0x10u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use a 16-byte (truncated) hash to confirm length encoding scales.
var short_hash: [u8] = []
var i: u64 = 0
while i < 16:
    short_hash.push(0x55u8)
    i = i + 1
val msg = build_hrr_synthetic_message_hash(short_hash)
expect(msg.len().to_u64()).to_equal(20u64)
expect(msg[0]).to_equal(0xFEu8)
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x10u8)
```

</details>

### build_client_hello2_bytes structure

#### places the same client_random in CH2 as CH1

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val random = _ch1_random_fixture()
val pub_key = _fresh_x25519_pub()
val ch2 = build_client_hello2_bytes(random, pub_key, "example.com", [])
# CH2 layout: type(1=HS_CLIENT_HELLO=0x01) + len(3) + legacy_version(2) + random(32) + ...
expect(ch2[0]).to_equal(0x01u8)  # HS_CLIENT_HELLO
# Random starts at offset 6 (1 + 3 + 2).
var i: u64 = 0
while i < 32:
    expect(ch2[6 + i]).to_equal(random[i])
    i = i + 1
```

</details>

#### embeds a fresh key_share with the supplied pub_key

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val random = _ch1_random_fixture()
val pub_key = _fresh_x25519_pub()
val ch2 = build_client_hello2_bytes(random, pub_key, "example.com", [])
# The 32-byte fresh pub_key must appear somewhere in CH2.
val idx = _byte_index_of(ch2, pub_key)
expect(idx.to_i64() >= 0).to_equal(true)
```

</details>

#### echoes a non-empty cookie verbatim into CH2

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val random = _ch1_random_fixture()
val pub_key = _fresh_x25519_pub()
val cookie: [u8] = [0xCAu8, 0xFEu8, 0xBAu8, 0xBEu8, 0xDEu8, 0xADu8]
val ch2 = build_client_hello2_bytes(random, pub_key, "example.com", cookie)
# Cookie bytes must appear after a 0x002C extension type marker.
val idx = _byte_index_of(ch2, cookie)
expect(idx.to_i64() >= 0).to_equal(true)
# And the EXT_COOKIE = 44 = 0x002C marker should appear at idx-4.
expect(EXT_COOKIE).to_equal(44u16)
# idx points to start of cookie bytes which is 2 (cookie u16 len) bytes
# after data start, which is 4 bytes after ext_type. So ext_type at idx-6.
# Verify presence of the 0x00 0x2C type pair in CH2 bytes.
val ck_marker: [u8] = [0x00u8, 0x2Cu8]
val mark_idx = _byte_index_of(ch2, ck_marker)
expect(mark_idx.to_i64() >= 0).to_equal(true)
```

</details>

#### omits the cookie extension when caller passes an empty cookie

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val random = _ch1_random_fixture()
val pub_key = _fresh_x25519_pub()
val ch2_no_cookie = build_client_hello2_bytes(random, pub_key, "example.com", [])
val ch2_with_cookie = build_client_hello2_bytes(random, pub_key, "example.com", [0xAAu8, 0xBBu8])
# CH2 with cookie must be strictly longer.
expect(ch2_no_cookie.len() < ch2_with_cookie.len()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/hello_retry_request_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HRR magic-bytes detection
- parse_hello_retry_request happy paths
- parse_hello_retry_request rejections
- build_hrr_synthetic_message_hash byte-exact format
- build_client_hello2_bytes structure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
