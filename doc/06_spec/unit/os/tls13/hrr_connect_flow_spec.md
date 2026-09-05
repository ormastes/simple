# Hrr Connect Flow Specification

> Tests covering process_hrr_after_serverhello AC-1 second-HRR rejection, process_hrr_after_serverhello AC-2 same-group rejection, process_hrr_after_serverhello AC-3 CH2 routing for SECP256R1, process_hrr_after_serverhello AC-4 transcript replacement (§4.4.1).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hrr Connect Flow Specification

## Scenarios

### process_hrr_after_serverhello AC-1 second-HRR rejection

#### rejects with unexpected_message when seen_hrr is already true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects with unexpected_message when seen_hrr is already true
   - Expected: reason contains `unexpected_message`
   - Expected: reason contains `second HRR`
   - Expected: "expected Reject(second HRR)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects with unexpected_message when seen_hrr is already true")
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

- rejects when HRR picks GROUP_X25519 and CH1 already offered X25519
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `X25519`
   - Expected: "expected Reject(same-group X25519)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when HRR picks GROUP_X25519 and CH1 already offered X25519")
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

- rejects when HRR picks SECP256R1 and CH1 already offered SECP256R1
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `secp256r1`
   - Expected: "expected Reject(same-group secp256r1)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when HRR picks SECP256R1 and CH1 already offered SECP256R1")
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

- rejects when HRR picks an unadvertised group
   - Expected: reason contains `illegal_parameter`
   - Expected: reason contains `not in client supported_groups`
   - Expected: "expected Reject(unsupported group)" equals `got Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when HRR picks an unadvertised group")
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

- builds CH2 with P-256 key_share when CH1 only advertised X25519
   - Expected: value.selected_group equals `GROUP_SECP256R1`
   - Expected: value.client_hello2_bytes[0] equals `0x01u8`
   - Expected: value.client_hello2_bytes[6 + i] equals `_ch1_random()[i]`
   - Expected: "expected Ok(P-256 CH2)" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds CH2 with P-256 key_share when CH1 only advertised X25519")
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

- preserves CH1 client_random verbatim in CH2 (RFC 8446 §4.1.2)
   - Expected: value.client_hello2_bytes[6 + i] equals `_ch1_random()[i]`
   - Expected: "expected Ok" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves CH1 client_random verbatim in CH2 (RFC 8446 §4.1.2)")
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

- echoes a non-empty cookie verbatim as a contiguous run inside CH2
   - Expected: _contains_run(ch2, cookie) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("echoes a non-empty cookie verbatim as a contiguous run inside CH2")
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

- transcript_seed starts with synthetic message_hash 0xfe 0x00 0x00 0x20 || Hash(CH1)
   - Expected: seed[0] equals `HS_MESSAGE_HASH)         # 0xfe`
   - Expected: seed[1] equals `0x00u8`
   - Expected: seed[2] equals `0x00u8`
   - Expected: seed[3] equals `0x20u8)                  # SHA-256 length`
   - Expected: seed[4 + i] equals `ch1h[i]`
   - Expected: "expected Ok" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transcript_seed starts with synthetic message_hash 0xfe 0x00 0x00 0x20 || Hash(CH1)")
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

- transcript_seed appends HRR handshake bytes verbatim after synthetic prefix
   - Expected: seed.len() equals `(36u64 + hs.len().to_u64())`
   - Expected: seed[36 + i] equals `hs[i]`
   - Expected: "expected Ok" equals `got Reject`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transcript_seed appends HRR handshake bytes verbatim after synthetic prefix")
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
| Source | `test/unit/os/tls13/hrr_connect_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering process_hrr_after_serverhello AC-1 second-HRR rejection, process_hrr_after_serverhello AC-2 same-group rejection, process_hrr_after_serverhello AC-3 CH2 routing for SECP256R1, process_hrr_after_serverhello AC-4 transcript replacement (§4.4.1).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `351346906e5ddce7060d1a39aab7c1b6ca97d02cb7fa94d4975600c51ca71f42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `351346906e5ddce7060d1a39aab7c1b6ca97d02cb7fa94d4975600c51ca71f42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `351346906e5ddce7060d1a39aab7c1b6ca97d02cb7fa94d4975600c51ca71f42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/hrr_connect_flow_spec.spl
mirror: doc/06_spec/unit/os/tls13/hrr_connect_flow_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/hrr_connect_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/hrr_connect_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/hrr_connect_flow_spec.spl:242:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects with unexpected_message when seen_hrr is already true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/hrr_connect_flow_spec.spl:262:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects when HRR picks GROUP_X25519 and CH1 already offered X25519' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/hrr_connect_flow_spec.spl:280:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects when HRR picks SECP256R1 and CH1 already offered SECP256R1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
