# new_session_ticket_spec

> Verifies the new session ticket behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# new_session_ticket_spec

Verifies the new session ticket behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/new_session_ticket_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the new session ticket behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### NewSessionTicket — RFC 8446 §4.6.1

#### encode body: fixed fields at correct offsets

- Verify: encode body: fixed fields at correct offsets
   - Expected: _u32_be(enc, 0u64) equals `7200u32`
   - Expected: _u32_be(enc, 4u64) equals `0xDEADBEEFu32`
   - Expected: enc[8].to_u32() equals `4u32`
   - Expected: enc[9].to_u32() equals `0x01u32`
   - Expected: enc[12].to_u32() equals `0x04u32`
   - Expected: _u16_be(enc, 13u64) equals `16u32`
   - Expected: _u16_be(enc, 31u64) equals `0u32`
   - Expected: enc.len() equals `33)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: encode body: fixed fields at correct offsets")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nst = _build_nst()
val enc = encode_new_session_ticket(nst)
# ticket_lifetime at offset 0 = 7200 = 0x00001C20
expect(_u32_be(enc, 0u64)).to_equal(7200u32)
# ticket_age_add at offset 4
expect(_u32_be(enc, 4u64)).to_equal(0xDEADBEEFu32)
# ticket_nonce length byte at offset 8 = 4
expect(enc[8].to_u32()).to_equal(4u32)
# nonce bytes 0x01 0x02 0x03 0x04 at offset 9..12
expect(enc[9].to_u32()).to_equal(0x01u32)
expect(enc[12].to_u32()).to_equal(0x04u32)
# ticket length at offset 13 = 16 = 0x0010
expect(_u16_be(enc, 13u64)).to_equal(16u32)
# extensions length at offset 31 = 0 (no extensions)
expect(_u16_be(enc, 31u64)).to_equal(0u32)
# total length: 4+4+1+4+2+16+2 = 33
expect(enc.len()).to_equal(33)  # oracle: pinned constant asserted by this scenario
```

</details>

#### encode body round-trip: all fields preserved

- Verify: encode body round-trip: all fields preserved
   - Expected: d.ok is true
   - Expected: d.nst.ticket_lifetime equals `7200u32`
   - Expected: d.nst.ticket_age_add equals `0xDEADBEEFu32`
   - Expected: _bytes_eq(d.nst.ticket_nonce, _seq_n(4u64, 0x01u8)) is true
   - Expected: _bytes_eq(d.nst.ticket, _seq_n(16u64, 0xAAu8)) is true
   - Expected: d.nst.extensions.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: encode body round-trip: all fields preserved")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val d = _encode_and_decode(_build_nst())
expect(d.ok).to_equal(true)
expect(d.nst.ticket_lifetime).to_equal(7200u32)
expect(d.nst.ticket_age_add).to_equal(0xDEADBEEFu32)
expect(_bytes_eq(d.nst.ticket_nonce, _seq_n(4u64, 0x01u8))).to_equal(true)
expect(_bytes_eq(d.nst.ticket, _seq_n(16u64, 0xAAu8))).to_equal(true)
expect(d.nst.extensions.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### encode body round-trip: non-empty extensions preserved

- Verify: encode body round-trip: non-empty extensions preserved
   - Expected: d.ok is true
   - Expected: d.nst.ticket_lifetime equals `3600u32`
   - Expected: d.nst.extensions.len() equals `8)  # oracle: pinned constant asserted by this scenario`
   - Expected: _bytes_eq(d.nst.extensions, nst.extensions) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: encode body round-trip: non-empty extensions preserved")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nst = _build_nst_with_ext()
val d = _encode_and_decode(nst)
expect(d.ok).to_equal(true)
expect(d.nst.ticket_lifetime).to_equal(3600u32)
expect(d.nst.extensions.len()).to_equal(8)  # oracle: pinned constant asserted by this scenario
expect(_bytes_eq(d.nst.extensions, nst.extensions)).to_equal(true)
```

</details>

#### handshake wrap: type byte is 0x04

- Verify: handshake wrap: type byte is 0x04
   - Expected: enc[0].to_u32() equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: handshake wrap: type byte is 0x04")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val enc = encode_new_session_ticket_handshake(_build_nst())
expect(enc[0].to_u32()).to_equal(4u32)
```

</details>

#### handshake wrap: uint24 length matches body

- Verify: handshake wrap: uint24 length matches body
   - Expected: decoded_len equals `body.len().to_u32()`
   - Expected: wrapped.len() equals `4 + body.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: handshake wrap: uint24 length matches body")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: handshake round-trip via decode_new_session_ticket_handshake
   - Expected: d.ok is true
   - Expected: d.nst.ticket_lifetime equals `7200u32`
   - Expected: d.nst.ticket_age_add equals `0xDEADBEEFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: handshake round-trip via decode_new_session_ticket_handshake")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val d = _encode_decode_handshake(_build_nst())
expect(d.ok).to_equal(true)
expect(d.nst.ticket_lifetime).to_equal(7200u32)
expect(d.nst.ticket_age_add).to_equal(0xDEADBEEFu32)
```

</details>

#### decode rejects zero-length ticket

- Verify: decode rejects zero-length ticket
   - Expected: d.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: decode rejects zero-length ticket")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: decode rejects truncated buffer
   - Expected: d.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: decode rejects truncated buffer")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val enc = encode_new_session_ticket(_build_nst())
# truncate to first 5 bytes
val short = _nst_slice_helper(enc, 0u64, 5u64)
val d = decode_new_session_ticket(short)
expect(d.ok).to_equal(false)
```

</details>

#### handshake decode rejects wrong HandshakeType

- Verify: handshake decode rejects wrong HandshakeType
   - Expected: d.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: handshake decode rejects wrong HandshakeType")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: derive_resumption_psk_from_ticket returns 32 bytes for SHA-256 path
   - Expected: psk.len() equals `32)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: derive_resumption_psk_from_ticket returns 32 bytes for SHA-256 path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val rms = _seq_n(32u64, 0x55u8)
val nonce = _seq_n(4u64, 0x01u8)
val psk = derive_resumption_psk_from_ticket(rms, nonce, 1u8)
expect(psk.len()).to_equal(32)  # oracle: pinned constant asserted by this scenario
```

</details>

#### derive_resumption_psk_from_ticket is deterministic

- Verify: derive_resumption_psk_from_ticket is deterministic
   - Expected: _derive_psk_twice(rms, nonce) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: derive_resumption_psk_from_ticket is deterministic")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val rms = _seq_n(32u64, 0x77u8)
val nonce = _seq_n(3u64, 0x22u8)
expect(_derive_psk_twice(rms, nonce)).to_equal(true)
```

</details>

#### derive_resumption_psk_from_ticket matches tls13_resumption_secret

- Verify: derive_resumption_psk_from_ticket matches tls13_resumption_secret
   - Expected: _psk_matches_key_schedule(rms, nonce) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: derive_resumption_psk_from_ticket matches tls13_resumption_secret")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val rms = _seq_n(32u64, 0x33u8)
val nonce = _seq_n(2u64, 0xFFu8)
expect(_psk_matches_key_schedule(rms, nonce)).to_equal(true)
```

</details>

#### stored_psk_from_new_session_ticket: ticket fields copied correctly

- Verify: stored_psk_from_new_session_ticket: ticket fields copied correctly
   - Expected: sp.lifetime_seconds equals `7200u32`
   - Expected: sp.age_add equals `0xDEADBEEFu32`
   - Expected: sp.cipher_suite equals `0x1301u16`
   - Expected: _bytes_eq(sp.ticket, _seq_n(16u64, 0xAAu8)) is true
   - Expected: _bytes_eq(sp.ticket_nonce, _seq_n(4u64, 0x01u8)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: stored_psk_from_new_session_ticket: ticket fields copied correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: stored_psk_from_new_session_ticket: derived PSK matches direct derivation
   - Expected: _stored_psk_from_nst_psk_matches(nst, rms) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: stored_psk_from_new_session_ticket: derived PSK matches direct derivation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val nst = _build_nst()
val rms = _seq_n(32u64, 0xCCu8)
expect(_stored_psk_from_nst_psk_matches(nst, rms)).to_equal(true)
```

</details>

#### RMS derivation produces 32 bytes for SHA-256

- Verify: RMS derivation produces 32 bytes for SHA-256
   - Expected: _rms_sha256_len_correct(master, thash) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: RMS derivation produces 32 bytes for SHA-256")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val master = _seq_n(32u64, 0x11u8)
val thash = _seq_n(32u64, 0x22u8)
expect(_rms_sha256_len_correct(master, thash)).to_equal(true)
```

</details>

#### RMS derivation is deterministic

- Verify: RMS derivation is deterministic
   - Expected: _rms_sha256_deterministic(master, thash) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: RMS derivation is deterministic")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val master = _seq_n(32u64, 0xAAu8)
val thash = _seq_n(32u64, 0xBBu8)
expect(_rms_sha256_deterministic(master, thash)).to_equal(true)
```

</details>

#### full pipeline: master_secret → RMS → StoredPsk PSK matches direct derivation

- Verify: full pipeline: master_secret → RMS → StoredPsk PSK matches direct derivation
   - Expected: _full_pipeline_psk_matches_direct(master, thash, nst) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: full pipeline: master_secret → RMS → StoredPsk PSK matches direct derivation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val master = _seq_n(32u64, 0x42u8)
val thash = _seq_n(32u64, 0x99u8)
val nst = _build_nst()
expect(_full_pipeline_psk_matches_direct(master, thash, nst)).to_equal(true)
```

</details>

#### full pipeline: StoredPsk fields copied from NST

- Verify: full pipeline: StoredPsk fields copied from NST
   - Expected: sp.lifetime_seconds equals `7200u32`
   - Expected: sp.age_add equals `0xDEADBEEFu32`
   - Expected: sp.cipher_suite equals `0x1301u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: full pipeline: StoredPsk fields copied from NST")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: handshake-wrapped NST decode → StoredPsk end-to-end
   - Expected: _nst_handshake_decode_to_store(rms) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_NEW_SESSION_TICKET-001
step("Verify: handshake-wrapped NST decode → StoredPsk end-to-end")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val rms = _seq_n(32u64, 0x55u8)
expect(_nst_handshake_decode_to_store(rms)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b95ee25708a92fe3f7664f5b5034453c2123e6b8cb6f4d8a8c75a947dfb5eceb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b95ee25708a92fe3f7664f5b5034453c2123e6b8cb6f4d8a8c75a947dfb5eceb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b95ee25708a92fe3f7664f5b5034453c2123e6b8cb6f4d8a8c75a947dfb5eceb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/tls13/new_session_ticket_spec.spl
mirror: doc/06_spec/01_unit/os/tls13/new_session_ticket_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tls13/new_session_ticket_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/tls13/new_session_ticket_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tls13/new_session_ticket_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
