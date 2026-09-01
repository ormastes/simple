# New Session Ticket Specification

> Tests covering NewSessionTicket — RFC 8446 §4.6.1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# New Session Ticket Specification

## Scenarios

### NewSessionTicket — RFC 8446 §4.6.1

#### encode body: fixed fields at correct offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### encode body round-trip: all fields preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _encode_and_decode(_build_nst())
expect(d.ok).to_equal(true)
expect(d.nst.ticket_lifetime).to_equal(7200u32)
expect(d.nst.ticket_age_add).to_equal(0xDEADBEEFu32)
expect(_bytes_eq(d.nst.ticket_nonce, _seq_n(4u64, 0x01u8))).to_equal(true)
expect(_bytes_eq(d.nst.ticket, _seq_n(16u64, 0xAAu8))).to_equal(true)
expect(d.nst.extensions.len()).to_equal(0)
```

</details>

#### encode body round-trip: non-empty extensions preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nst = _build_nst_with_ext()
val d = _encode_and_decode(nst)
expect(d.ok).to_equal(true)
expect(d.nst.ticket_lifetime).to_equal(3600u32)
expect(d.nst.extensions.len()).to_equal(8)
expect(_bytes_eq(d.nst.extensions, nst.extensions)).to_equal(true)
```

</details>

#### handshake wrap: type byte is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = encode_new_session_ticket_handshake(_build_nst())
expect(enc[0].to_u32()).to_equal(4u32)
```

</details>

#### handshake wrap: uint24 length matches body

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nst = _build_nst()
val body = encode_new_session_ticket(nst)
val wrapped = encode_new_session_ticket_handshake(nst)
val body_len_hi = wrapped[1].to_u32()
val body_len_mid = wrapped[2].to_u32()
val body_len_lo = wrapped[3].to_u32()
val decoded_len = (body_len_hi << 16) | (body_len_mid << 8) | body_len_lo
expect(decoded_len).to_equal(body.len().to_u32())
# total wrapped length = 4 header + body
expect(wrapped.len()).to_equal(4 + body.len())
```

</details>

#### handshake round-trip via decode_new_session_ticket_handshake

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = _encode_decode_handshake(_build_nst())
expect(d.ok).to_equal(true)
expect(d.nst.ticket_lifetime).to_equal(7200u32)
expect(d.nst.ticket_age_add).to_equal(0xDEADBEEFu32)
```

</details>

#### decode rejects zero-length ticket

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nst = NewSessionTicket(
    ticket_lifetime: 100u32,
    ticket_age_add: 1u32,
    ticket_nonce: _seq_n(2u64, 0x01u8),
    ticket: [],
    extensions: [],
)
val enc = encode_new_session_ticket(nst)
val d = decode_new_session_ticket(enc)
expect(d.ok).to_equal(false)
```

</details>

#### decode rejects truncated buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = encode_new_session_ticket(_build_nst())
# truncate to first 5 bytes
val short = _nst_slice_helper(enc, 0u64, 5u64)
val d = decode_new_session_ticket(short)
expect(d.ok).to_equal(false)
```

</details>

#### handshake decode rejects wrong HandshakeType

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = encode_new_session_ticket_handshake(_build_nst())
# replace type byte (0x04) with 0x02 (ServerHello)
var tampered: [u8] = []
tampered.push(0x02u8)
var i: u64 = 1
val n = enc.len().to_u64()
while i < n:
    tampered.push(enc[i.to_i64()])
    i = i + 1
val d = decode_new_session_ticket_handshake(tampered)
expect(d.ok).to_equal(false)
```

</details>

#### derive_resumption_psk_from_ticket returns 32 bytes for SHA-256 path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rms = _seq_n(32u64, 0x55u8)
val nonce = _seq_n(4u64, 0x01u8)
val psk = derive_resumption_psk_from_ticket(rms, nonce, 1u8)
expect(psk.len()).to_equal(32)
```

</details>

#### derive_resumption_psk_from_ticket is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rms = _seq_n(32u64, 0x77u8)
val nonce = _seq_n(3u64, 0x22u8)
expect(_derive_psk_twice(rms, nonce)).to_equal(true)
```

</details>

#### derive_resumption_psk_from_ticket matches tls13_resumption_secret

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rms = _seq_n(32u64, 0x33u8)
val nonce = _seq_n(2u64, 0xFFu8)
expect(_psk_matches_key_schedule(rms, nonce)).to_equal(true)
```

</details>

#### stored_psk_from_new_session_ticket: ticket fields copied correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nst = _build_nst()
val rms = _zeros_n(32u64)
val sp = stored_psk_from_new_session_ticket(nst, rms, 1u8, 0x1301u16)
expect(sp.lifetime_seconds).to_equal(7200u32)
expect(sp.age_add).to_equal(0xDEADBEEFu32)
expect(sp.cipher_suite).to_equal(0x1301u16)
expect(_bytes_eq(sp.ticket, _seq_n(16u64, 0xAAu8))).to_equal(true)
expect(_bytes_eq(sp.ticket_nonce, _seq_n(4u64, 0x01u8))).to_equal(true)
```

</details>

#### stored_psk_from_new_session_ticket: derived PSK matches direct derivation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nst = _build_nst()
val rms = _seq_n(32u64, 0xCCu8)
expect(_stored_psk_from_nst_psk_matches(nst, rms)).to_equal(true)
```

</details>

#### RMS derivation produces 32 bytes for SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _seq_n(32u64, 0x11u8)
val thash = _seq_n(32u64, 0x22u8)
expect(_rms_sha256_len_correct(master, thash)).to_equal(true)
```

</details>

#### RMS derivation is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _seq_n(32u64, 0xAAu8)
val thash = _seq_n(32u64, 0xBBu8)
expect(_rms_sha256_deterministic(master, thash)).to_equal(true)
```

</details>

#### full pipeline: master_secret → RMS → StoredPsk PSK matches direct derivation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _seq_n(32u64, 0x42u8)
val thash = _seq_n(32u64, 0x99u8)
val nst = _build_nst()
expect(_full_pipeline_psk_matches_direct(master, thash, nst)).to_equal(true)
```

</details>

#### full pipeline: StoredPsk fields copied from NST

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val master = _seq_n(32u64, 0x7Fu8)
val thash = _seq_n(32u64, 0x3Cu8)
val nst = _build_nst()
val sp = _full_pipeline_psk(master, thash, nst)
expect(sp.lifetime_seconds).to_equal(7200u32)
expect(sp.age_add).to_equal(0xDEADBEEFu32)
expect(sp.cipher_suite).to_equal(0x1301u16)
```

</details>

#### handshake-wrapped NST decode → StoredPsk end-to-end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rms = _seq_n(32u64, 0x55u8)
expect(_nst_handshake_decode_to_store(rms)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/new_session_ticket_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NewSessionTicket — RFC 8446 §4.6.1.
- NewSessionTicket — RFC 8446 §4.6.1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `56191da0b5ed8f8d1cd9f2df869cca6fab600e69c3abb6334386008e7c6a9b1f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56191da0b5ed8f8d1cd9f2df869cca6fab600e69c3abb6334386008e7c6a9b1f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56191da0b5ed8f8d1cd9f2df869cca6fab600e69c3abb6334386008e7c6a9b1f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/os/tls13/new_session_ticket_spec.spl
mirror: doc/06_spec/unit/os/tls13/new_session_ticket_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/new_session_ticket_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/new_session_ticket_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/new_session_ticket_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/os/tls13/new_session_ticket_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/tls13/new_session_ticket_spec.spl:146:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'encode body: fixed fields at correct offsets' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/tls13/new_session_ticket_spec.spl:167:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'encode body round-trip: all fields preserved' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/tls13/new_session_ticket_spec.spl:176:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'encode body round-trip: non-empty extensions preserved' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/os/tls13/new_session_ticket_spec.spl:184:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'handshake wrap: type byte is 0x04' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
