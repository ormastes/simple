# Hrr Connect Flow Specification

> 1. hs, body,  ch1 random

<!-- sdn-diagram:id=hrr_connect_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hrr_connect_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hrr_connect_flow_spec -> std
hrr_connect_flow_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hrr_connect_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hrr Connect Flow Specification

## Scenarios

### process_hrr_after_serverhello AC-1 second-HRR rejection

#### rejects with unexpected_message when seen_hrr is already true

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: reason contains `unexpected_message`
   - Expected: reason contains `second HRR`
   - Expected: "expected Reject(second HRR)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_p256_no_cookie_hs()
val body = _hrr_p256_no_cookie_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    true,   # seen_hrr — second HRR
    true,   # ch1_offered_x25519
    true,   # ch1_offered_p256
)
if val HrrFlowResult.Reject(reason) = r:
    expect(reason.contains("unexpected_message")).to_equal(true)
    expect(reason.contains("second HRR")).to_equal(true)
else:
    expect("expected Reject(second HRR)").to_equal("got Ok")
```

</details>

### process_hrr_after_serverhello AC-2 same-group rejection

#### rejects when HRR picks GROUP_X25519 and CH1 already offered X25519

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `X25519`
   - Expected: "expected Reject(same-group X25519)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_x25519_no_cookie_hs()
val body = _hrr_x25519_no_cookie_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false,  # seen_hrr
    true,   # ch1_offered_x25519
    true,   # ch1_offered_p256
)
if val HrrFlowResult.Reject(reason) = r:
    expect(reason.contains("illegal_parameter")).to_equal(true)
    expect(reason.contains("X25519")).to_equal(true)
else:
    expect("expected Reject(same-group X25519)").to_equal("got Ok")
```

</details>

#### rejects when HRR picks SECP256R1 and CH1 already offered SECP256R1

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `secp256r1`
   - Expected: "expected Reject(same-group secp256r1)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_p256_no_cookie_hs()
val body = _hrr_p256_no_cookie_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false,
    true,   # ch1_offered_x25519
    true,   # ch1_offered_p256 — server has nothing to switch to
)
if val HrrFlowResult.Reject(reason) = r:
    expect(reason.contains("illegal_parameter")).to_equal(true)
    expect(reason.contains("secp256r1")).to_equal(true)
else:
    expect("expected Reject(same-group secp256r1)").to_equal("got Ok")
```

</details>

#### rejects when HRR picks an unadvertised group

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `not in client supported_groups`
   - Expected: "expected Reject(unsupported group)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_unsupported_group_hs()
val body = _hrr_unsupported_group_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false, true, true,
)
if val HrrFlowResult.Reject(reason) = r:
    expect(reason.contains("illegal_parameter")).to_equal(true)
    expect(reason.contains("not in client supported_groups")).to_equal(true)
else:
    expect("expected Reject(unsupported group)").to_equal("got Ok")
```

</details>

### process_hrr_after_serverhello AC-3 CH2 routing for SECP256R1

#### builds CH2 with P-256 key_share when CH1 only advertised X25519

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: value.selected_group equals `GROUP_SECP256R1`
   - Expected: value.client_hello2_bytes[0] equals `0x01u8`
   - Expected: value.client_hello2_bytes[6 + i] equals `_ch1_random()[i]`
   - Expected: "expected Ok(P-256 CH2)" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_p256_no_cookie_hs()
val body = _hrr_p256_no_cookie_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false,
    true,   # ch1_offered_x25519
    false,  # ch1_offered_p256 — server is allowed to pick secp256r1
)
if val HrrFlowResult.Ok(value) = r:
    expect(value.selected_group).to_equal(GROUP_SECP256R1)
    # CH2 first byte is HS_CLIENT_HELLO (0x01)
    expect(value.client_hello2_bytes[0]).to_equal(0x01u8)
    # CH2 random echoes CH1
    var i: u64 = 0
    while i < 32:
        expect(value.client_hello2_bytes[6 + i]).to_equal(_ch1_random()[i])
        i = i + 1
else:
    expect("expected Ok(P-256 CH2)").to_equal("got Reject")
```

</details>

#### preserves CH1 client_random verbatim in CH2 (RFC 8446 §4.1.2)

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: value.client_hello2_bytes[6 + i] equals `_ch1_random()[i]`
   - Expected: "expected Ok" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_p256_no_cookie_hs()
val body = _hrr_p256_no_cookie_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false, true, false,
)
if val HrrFlowResult.Ok(value) = r:
    # CH2 layout: 0x01 + 3-byte len + 0x0303 + random[32] starting at offset 6
    var i: u64 = 0
    while i < 32:
        expect(value.client_hello2_bytes[6 + i]).to_equal(_ch1_random()[i])
        i = i + 1
else:
    expect("expected Ok").to_equal("got Reject")
```

</details>

#### echoes a non-empty cookie verbatim as a contiguous run inside CH2

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: _contains_run(ch2, cookie) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cookie: [u8] = [0xCAu8, 0xFEu8, 0xBAu8, 0xBEu8, 0x01u8, 0x02u8]
val hs = _hrr_p256_with_cookie_hs(cookie)
val body = _hrr_p256_with_cookie_body(cookie)
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false, true, false,
)
val ch2 = _ch2_or_empty(r)
expect(_contains_run(ch2, cookie)).to_equal(true)
```

</details>

### process_hrr_after_serverhello AC-4 transcript replacement (§4.4.1)

#### transcript_seed starts with synthetic message_hash 0xfe 0x00 0x00 0x20 || Hash(CH1)

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: seed[0] equals `HS_MESSAGE_HASH)         # 0xfe`
   - Expected: seed[1] equals `0x00u8`
   - Expected: seed[2] equals `0x00u8`
   - Expected: seed[3] equals `0x20u8)                  # SHA-256 length`
   - Expected: seed[4 + i] equals `ch1h[i]`
   - Expected: "expected Ok" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_p256_no_cookie_hs()
val body = _hrr_p256_no_cookie_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false, true, false,
)
if val HrrFlowResult.Ok(value) = r:
    val seed = value.transcript_seed
    expect(seed[0]).to_equal(HS_MESSAGE_HASH)         # 0xfe
    expect(seed[1]).to_equal(0x00u8)
    expect(seed[2]).to_equal(0x00u8)
    expect(seed[3]).to_equal(0x20u8)                  # SHA-256 length
    # Bytes 4..36 must equal CH1 hash.
    val ch1h = _ch1_hash_fixture()
    var i: u64 = 0
    while i < 32:
        expect(seed[4 + i]).to_equal(ch1h[i])
        i = i + 1
else:
    expect("expected Ok").to_equal("got Reject")
```

</details>

#### transcript_seed appends HRR handshake bytes verbatim after synthetic prefix

1. hs, body,  ch1 random
2.  fresh x25519 pub
   - Expected: seed.len() equals `(36u64 + hs.len().to_u64())`
   - Expected: seed[36 + i] equals `hs[i]`
   - Expected: "expected Ok" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hs = _hrr_p256_no_cookie_hs()
val body = _hrr_p256_no_cookie_body()
val r = process_hrr_after_serverhello(
    hs, body, _ch1_random(), _fresh_x25519_pub(), _ch1_hash_fixture(),
    _fresh_x25519_pub(), _fresh_p256_pub(), "example.com",
    false, true, false,
)
if val HrrFlowResult.Ok(value) = r:
    val seed = value.transcript_seed
    # Prefix length = 4 (header) + 32 (hash) = 36
    expect(seed.len()).to_equal((36u64 + hs.len().to_u64()))
    var i: u64 = 0
    while i < hs.len():
        expect(seed[36 + i]).to_equal(hs[i])
        i = i + 1
else:
    expect("expected Ok").to_equal("got Reject")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/hrr_connect_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- process_hrr_after_serverhello AC-1 second-HRR rejection
- process_hrr_after_serverhello AC-2 same-group rejection
- process_hrr_after_serverhello AC-3 CH2 routing for SECP256R1
- process_hrr_after_serverhello AC-4 transcript replacement (§4.4.1)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
