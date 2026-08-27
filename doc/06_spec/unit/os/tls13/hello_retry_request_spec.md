# Hello Retry Request Specification

> Tests covering HRR magic-bytes detection, parse_hello_retry_request happy paths, parse_hello_retry_request rejections, build_hrr_synthetic_message_hash byte-exact format, build_client_hello2_bytes structure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hello Retry Request Specification

## Scenarios

### HRR magic-bytes detection

#### detects HRR when ServerHello.random == HRR_MAGIC

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects HRR when ServerHello.random == HRR_MAGIC
   - Expected: is_hello_retry_request(sh) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects HRR when ServerHello.random == HRR_MAGIC")
val sh = ServerHello13(random: _hrr_random_bytes(), cipher_suite: 0x1301u16, x25519_pub: [], p256_pub: [])
expect(is_hello_retry_request(sh)).to_equal(true)
```

</details>

#### rejects ServerHello whose random differs by even one byte

- rejects ServerHello whose random differs by even one byte
   - Expected: is_hello_retry_request(sh) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ServerHello whose random differs by even one byte")
val sh = ServerHello13(random: _flipped_random_bytes(), cipher_suite: 0x1301u16, x25519_pub: [], p256_pub: [])
expect(is_hello_retry_request(sh)).to_equal(false)
```

</details>

#### HRR_MAGIC is exactly 32 bytes and starts with 0xCF 0x21 0xAD 0x74

- HRR_MAGIC is exactly 32 bytes and starts with 0xCF 0x21 0xAD 0x74
   - Expected: HRR_MAGIC.len().to_u64() equals `32u64`
   - Expected: HRR_MAGIC[0] equals `0xCFu8`
   - Expected: HRR_MAGIC[1] equals `0x21u8`
   - Expected: HRR_MAGIC[2] equals `0xADu8`
   - Expected: HRR_MAGIC[3] equals `0x74u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HRR_MAGIC is exactly 32 bytes and starts with 0xCF 0x21 0xAD 0x74")
expect(HRR_MAGIC.len().to_u64()).to_equal(32u64)
expect(HRR_MAGIC[0]).to_equal(0xCFu8)
expect(HRR_MAGIC[1]).to_equal(0x21u8)
expect(HRR_MAGIC[2]).to_equal(0xADu8)
expect(HRR_MAGIC[3]).to_equal(0x74u8)
```

</details>

### parse_hello_retry_request happy paths

#### extracts cipher_suite, selected_group, and cookie when all present

- extracts cipher_suite, selected_group, and cookie when all present
   - Expected: value.cipher_suite equals `0x1301u16`
   - Expected: value.selected_group equals `0x0017u16`
   - Expected: value.cookie.len().to_u64() equals `4u64`
   - Expected: value.cookie[0] equals `0xCAu8`
   - Expected: value.cookie[1] equals `0xFEu8`
   - Expected: value.cookie[2] equals `0xBAu8`
   - Expected: value.cookie[3] equals `0xBEu8`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts cipher_suite, selected_group, and cookie when all present")
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
    expect(false).to_equal(true)
```

</details>

#### yields empty cookie when HRR omits the cookie extension

- yields empty cookie when HRR omits the cookie extension
   - Expected: value.selected_group equals `0x0017u16`
   - Expected: value.cookie.len().to_u64() equals `0u64`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields empty cookie when HRR omits the cookie extension")
val res = parse_hello_retry_request(_hrr_no_cookie())
if val HrrResult.Ok(value) = res:
    expect(value.selected_group).to_equal(0x0017u16)
    expect(value.cookie.len().to_u64()).to_equal(0u64)
else:
    expect(false).to_equal(true)
```

</details>

### parse_hello_retry_request rejections

#### rejects HRR with legacy_compression_method != 0x00

- rejects HRR with legacy_compression_method != 0x00
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `compression`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects HRR with legacy_compression_method != 0x00")
val res = parse_hello_retry_request(_hrr_bad_compression())
if val HrrResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
    expect(reason.contains("compression")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects HRR whose supported_versions != 0x0304

- rejects HRR whose supported_versions != 0x0304
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `supported_versions`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects HRR whose supported_versions != 0x0304")
val res = parse_hello_retry_request(_hrr_bad_supported_versions())
if val HrrResult.Err(reason) = res:
    expect(reason.contains("illegal_parameter")).to_equal(true)
    expect(reason.contains("supported_versions")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects HRR missing the key_share extension

- rejects HRR missing the key_share extension
   - Expected: reason contains `missing_extension`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects HRR missing the key_share extension")
val res = parse_hello_retry_request(_hrr_no_key_share())
if val HrrResult.Err(reason) = res:
    expect(reason.contains("missing_extension")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### rejects truncated HRR body (< 38 bytes)

- rejects truncated HRR body (< 38 bytes)
   - Expected: reason contains `decode_error`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated HRR body (< 38 bytes)")
val short_body: [u8] = [0x03u8, 0x03u8]
val res = parse_hello_retry_request(short_body)
if val HrrResult.Err(reason) = res:
    expect(reason.contains("decode_error")).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### still parses but flags same-group HRR via selected_group field

- still parses but flags same-group HRR via selected_group field
   - Expected: value.selected_group equals `GROUP_X25519`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still parses but flags same-group HRR via selected_group field")
# The wire-level parser cannot know what CH1 sent. The connect-flow
# caller is responsible for comparing parsed selected_group against
# CH1's offered group and rejecting if equal — RFC 8446 §4.1.4.
val res = parse_hello_retry_request(_hrr_same_group_x25519())
if val HrrResult.Ok(value) = res:
    expect(value.selected_group).to_equal(GROUP_X25519)
else:
    expect(false).to_equal(true)
```

</details>

### build_hrr_synthetic_message_hash byte-exact format

#### emits 0xfe 0x00 0x00 0x20 || Hash(CH1) for SHA-256 input

- emits 0xfe 0x00 0x00 0x20 || Hash(CH1) for SHA-256 input
   - Expected: msg.len().to_u64() equals `36u64`
   - Expected: msg[0] equals `0xFEu8`
   - Expected: msg[1] equals `0x00u8`
   - Expected: msg[2] equals `0x00u8`
   - Expected: msg[3] equals `0x20u8`
   - Expected: msg[4 + i] equals `ch1_hash[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 0xfe 0x00 0x00 0x20 || Hash(CH1) for SHA-256 input")
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

- uses the message_hash handshake type 254 (0xfe)
   - Expected: HS_MESSAGE_HASH equals `254u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the message_hash handshake type 254 (0xfe)")
expect(HS_MESSAGE_HASH).to_equal(254u8)
```

</details>

#### encodes hash length as big-endian u24 in handshake header

- encodes hash length as big-endian u24 in handshake header
   - Expected: msg.len().to_u64() equals `20u64`
   - Expected: msg[0] equals `0xFEu8`
   - Expected: msg[1] equals `0x00u8`
   - Expected: msg[2] equals `0x00u8`
   - Expected: msg[3] equals `0x10u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes hash length as big-endian u24 in handshake header")
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

- places the same client_random in CH2 as CH1
   - Expected: ch2[0] equals `0x01u8)  # HS_CLIENT_HELLO`
   - Expected: ch2[6 + i] equals `random[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places the same client_random in CH2 as CH1")
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

- embeds a fresh key_share with the supplied pub_key
   - Expected: idx.to_i64() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("embeds a fresh key_share with the supplied pub_key")
val random = _ch1_random_fixture()
val pub_key = _fresh_x25519_pub()
val ch2 = build_client_hello2_bytes(random, pub_key, "example.com", [])
# The 32-byte fresh pub_key must appear somewhere in CH2.
val idx = _byte_index_of(ch2, pub_key)
expect(idx.to_i64() >= 0).to_equal(true)
```

</details>

#### echoes a non-empty cookie verbatim into CH2

- echoes a non-empty cookie verbatim into CH2
   - Expected: idx.to_i64() >= 0 is true
   - Expected: EXT_COOKIE equals `44u16`
   - Expected: mark_idx.to_i64() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("echoes a non-empty cookie verbatim into CH2")
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

- omits the cookie extension when caller passes an empty cookie
   - Expected: ch2_no_cookie.len() < ch2_with_cookie.len() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits the cookie extension when caller passes an empty cookie")
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
| Source | `test/unit/os/tls13/hello_retry_request_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HRR magic-bytes detection, parse_hello_retry_request happy paths, parse_hello_retry_request rejections, build_hrr_synthetic_message_hash byte-exact format, build_client_hello2_bytes structure.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e82d943c9b2b6299ef3fa8cdd4699675a3cdc43d3c4fc3f241667b6af002d0c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e82d943c9b2b6299ef3fa8cdd4699675a3cdc43d3c4fc3f241667b6af002d0c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e82d943c9b2b6299ef3fa8cdd4699675a3cdc43d3c4fc3f241667b6af002d0c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/hello_retry_request_spec.spl
mirror: doc/06_spec/unit/os/tls13/hello_retry_request_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/hello_retry_request_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/hello_retry_request_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/hello_retry_request_spec.spl:195:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects HRR when ServerHello.random == HRR_MAGIC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/hello_retry_request_spec.spl:201:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects ServerHello whose random differs by even one byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/hello_retry_request_spec.spl:207:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HRR_MAGIC is exactly 32 bytes and starts with 0xCF 0x21 0xAD 0x74' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
