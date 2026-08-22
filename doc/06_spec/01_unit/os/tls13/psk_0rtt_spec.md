# psk_0rtt_spec

> Verifies the psk 0rtt behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# psk_0rtt_spec

Verifies the psk 0rtt behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/psk_0rtt_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the psk 0rtt behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### PSK + 0-RTT — RFC 8446 §4.2.11 + §4.2.10 + §7.1

#### PskIdentity wire encoding length: 2 + id_len + 4

- Verify: PskIdentity wire encoding length: 2 + id_len + 4
   - Expected: out.len() equals `11)  # oracle: pinned constant asserted by this scenario`
   - Expected: out[0].to_u32() equals `0u32`
   - Expected: out[1].to_u32() equals `5u32`
   - Expected: out[7].to_u32() equals `0x01u32`
   - Expected: out[8].to_u32() equals `0x02u32`
   - Expected: out[9].to_u32() equals `0x03u32`
   - Expected: out[10].to_u32() equals `0x04u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: PskIdentity wire encoding length: 2 + id_len + 4")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val id = PskIdentity(identity: _seq_n(5u64, 0xA0u8), obfuscated_ticket_age: 0x01020304u32)
val out = encode_psk_identity(id)
# 2 (len) + 5 (identity) + 4 (age) = 11
expect(out.len()).to_equal(11)  # oracle: pinned constant asserted by this scenario
# identity length prefix
expect(out[0].to_u32()).to_equal(0u32)
expect(out[1].to_u32()).to_equal(5u32)
# age bytes (big-endian)
expect(out[7].to_u32()).to_equal(0x01u32)
expect(out[8].to_u32()).to_equal(0x02u32)
expect(out[9].to_u32()).to_equal(0x03u32)
expect(out[10].to_u32()).to_equal(0x04u32)
```

</details>

#### PskBinder wire encoding has 1-byte length prefix

- Verify: PskBinder wire encoding has 1-byte length prefix
   - Expected: out.len() equals `33)  # oracle: pinned constant asserted by this scenario`
   - Expected: out[0].to_u32() equals `32u32`
   - Expected: out[1].to_u32() equals `0xCCu32`
   - Expected: out[32].to_u32() equals `0xCCu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: PskBinder wire encoding has 1-byte length prefix")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val b = PskBinder(binder: _seq_n(32u64, 0xCCu8))
val out = encode_psk_binder(b)
expect(out.len()).to_equal(33)  # oracle: pinned constant asserted by this scenario
expect(out[0].to_u32()).to_equal(32u32)
expect(out[1].to_u32()).to_equal(0xCCu32)
expect(out[32].to_u32()).to_equal(0xCCu32)
```

</details>

#### OfferedPsks encode produces both identity and binder length frames

- Verify: OfferedPsks encode produces both identity and binder length frames
   - Expected: out.len() equals `51)  # oracle: pinned constant asserted by this scenario`
   - Expected: _u16_be(out, 0u64) equals `14u32`
   - Expected: _u16_be(out, 16u64) equals `33u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: OfferedPsks encode produces both identity and binder length frames")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val offer = _build_simple_offer()
val out = encode_offered_psk(offer)
# identities block:  uint16 len + (uint16 id_len + 8 + 4) = 2 + 14 = 16
# binders block:     uint16 len + (uint8 + 32) = 2 + 33 = 35
# total = 16 + 35 = 51
expect(out.len()).to_equal(51)  # oracle: pinned constant asserted by this scenario
# outer identities length = 14
expect(_u16_be(out, 0u64)).to_equal(14u32)
# binders length frame at offset 16 = 33
expect(_u16_be(out, 16u64)).to_equal(33u32)
```

</details>

#### OfferedPsks encode round-trips through decode

- Verify: OfferedPsks encode round-trips through decode
   - Expected: d.ok is true
   - Expected: d.psk.identities.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: d.psk.binders.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: got_id.obfuscated_ticket_age equals `0xDEADBEEFu32`
   - Expected: _bytes_eq(got_id.identity, _seq_n(8u64, 0x10u8)) is true
   - Expected: _bytes_eq(got_binder.binder, _seq_n(32u64, 0x20u8)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: OfferedPsks encode round-trips through decode")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val offer = _build_simple_offer()
val out = encode_offered_psk(offer)
val d = decode_offered_psk(out)
expect(d.ok).to_equal(true)
expect(d.psk.identities.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(d.psk.binders.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
val got_id = d.psk.identities[0]
expect(got_id.obfuscated_ticket_age).to_equal(0xDEADBEEFu32)
expect(_bytes_eq(got_id.identity, _seq_n(8u64, 0x10u8))).to_equal(true)
val got_binder = d.psk.binders[0]
expect(_bytes_eq(got_binder.binder, _seq_n(32u64, 0x20u8))).to_equal(true)
```

</details>

#### decode_offered_psk rejects truncated input

- Verify: decode_offered_psk rejects truncated input
   - Expected: d.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: decode_offered_psk rejects truncated input")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val short_input: [u8] = [0x00u8, 0x05u8]  # claims 5 bytes of identities, none follow
val d = decode_offered_psk(short_input)
expect(d.ok).to_equal(false)
```

</details>

#### decode_offered_psk rejects binder shorter than 32 bytes

- Verify: decode_offered_psk rejects binder shorter than 32 bytes
   - Expected: d.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: decode_offered_psk rejects binder shorter than 32 bytes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# build manually: 1 identity (id_len=2 + 2 bytes + 4 age = 8 bytes block; ids_len=8),
# then binders block with a single binder of length 16 (illegal)
var buf: [u8] = []
buf.push(0x00u8)
buf.push(0x08u8)            # ids_len = 8
buf.push(0x00u8)
buf.push(0x02u8)            # id_len = 2
buf.push(0xAAu8)
buf.push(0xBBu8)            # identity bytes
buf.push(0x00u8)
buf.push(0x00u8)
buf.push(0x00u8)
buf.push(0x01u8)            # age = 1
buf.push(0x00u8)
buf.push(0x11u8)            # binders_len = 17 (1 byte len prefix + 16 binder)
buf.push(0x10u8)            # binder len = 16 (illegal, < 32)
var i: u64 = 0
while i < 16:
    buf.push(0xFFu8)
    i = i + 1
val d = decode_offered_psk(buf)
expect(d.ok).to_equal(false)
```

</details>

#### encode_offered_psk_partial zeroes binders of declared lengths

- Verify: encode_offered_psk_partial zeroes binders of declared lengths
   - Expected: out.len() equals `47)  # oracle: pinned constant asserted by this scenario`
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: encode_offered_psk_partial zeroes binders of declared lengths")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ident = _seq_n(4u64, 0x44u8)
val ids: [PskIdentity] = [PskIdentity(identity: ident, obfuscated_ticket_age: 0u32)]
val lens: [u32] = [32u32]
val out = encode_offered_psk_partial(ids, lens)
# identities block: 2 (id_len) + 4 + 4 = 10  → ids_len=10 → outer 12
# binders block: 1 + 32 = 33  → 2 + 33 = 35
# total = 12 + 35 = 47
expect(out.len()).to_equal(47)  # oracle: pinned constant asserted by this scenario
# last 32 bytes (binder data) must all be zero
var ok = true
var i: u64 = 0
while i < 32:
    val byte = out[(out.len() - 32 + i.to_i64())]
    if byte.to_u32() != 0u32:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### early_secret_from_psk(zero_psk) byte-exact = HKDF-Extract(0^32, 0^32)

- Verify: early_secret_from_psk(zero_psk) byte-exact = HKDF-Extract(0^32, 0^32)
   - Expected: es.len() equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: early_secret_from_psk(zero_psk) byte-exact = HKDF-Extract(0^32, 0^32)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val zero32 = _zeros32()
val es = tls13_early_secret_from_psk(zero32, 1u8)
# Reference: HKDF-Extract(salt=0^32, IKM=0^32) — matches the all-zero
# PSK case which equals tls13_early_secret() result.
val ref_es = hkdf_extract(zero32, zero32)
# ref_es may be longer; compare first 32 bytes
expect(es.len()).to_equal(32)  # oracle: pinned constant asserted by this scenario
var ok = true
var i: u64 = 0
while i < 32:
    if es[i.to_i64()] != ref_es[i.to_i64()]:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### binder_key derivation length matches HashLen

- Verify: binder_key derivation length matches HashLen
   - Expected: bk_ext.len() equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: bk_res.len() equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: _bytes_eq(bk_ext, bk_res) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: binder_key derivation length matches HashLen")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val zero32 = _zeros32()
val es = tls13_early_secret_from_psk(zero32, 1u8)
val bk_ext = tls13_binder_key(es, 1u8, false)
val bk_res = tls13_binder_key(es, 1u8, true)
expect(bk_ext.len()).to_equal(32)  # oracle: pinned constant asserted by this scenario
expect(bk_res.len()).to_equal(32)  # oracle: pinned constant asserted by this scenario
# ext binder ≠ res binder
expect(_bytes_eq(bk_ext, bk_res)).to_equal(false)
```

</details>

#### psk binder MAC = HMAC-SHA-256(finished_key, transcript_hash)

- Verify: psk binder MAC = HMAC-SHA-256(finished_key, transcript_hash)
   - Expected: got_mac.len() equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: psk binder MAC = HMAC-SHA-256(finished_key, transcript_hash)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val zero32 = _zeros32()
val es = tls13_early_secret_from_psk(zero32, 1u8)
val bk = tls13_binder_key(es, 1u8, true)
# Independently compute finished_key = HKDF-Expand-Label(bk, "finished", "", 32)
val empty: [u8] = []
val fk = hkdf_expand_label(bk, "finished", empty, 32)
val th = _seq_n(32u64, 0x55u8)
val expected_mac = sha256_hmac(fk, th)
val got_mac = tls13_compute_psk_binder(bk, th, 1u8)
# both 32-byte
expect(got_mac.len()).to_equal(32)  # oracle: pinned constant asserted by this scenario
var ok = true
var i: u64 = 0
while i < 32:
    if got_mac[i.to_i64()] != expected_mac[i.to_i64()]:
        ok = false
    i = i + 1
expect(ok).to_equal(true)
```

</details>

#### client_early_traffic_secret derives non-zero 32-byte secret

- Verify: client_early_traffic_secret derives non-zero 32-byte secret
   - Expected: cets.len() equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: nonzero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: client_early_traffic_secret derives non-zero 32-byte secret")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val zero32 = _zeros32()
val es = tls13_early_secret_from_psk(zero32, 1u8)
val th = _seq_n(32u64, 0x77u8)
val cets = tls13_client_early_traffic_secret(es, th, 1u8)
expect(cets.len()).to_equal(32)  # oracle: pinned constant asserted by this scenario
# verify it's not all-zero (would indicate broken derivation)
var nonzero = false
var i: u64 = 0
while i < 32:
    if cets[i.to_i64()].to_u32() != 0u32:
        nonzero = true
    i = i + 1
expect(nonzero).to_equal(true)
```

</details>

#### StoredPsk constructor for external PSK initializes ticket fields

- Verify: StoredPsk constructor for external PSK initializes ticket fields
   - Expected: sp.cipher_suite equals `0x1301u16`
   - Expected: sp.lifetime_seconds equals `0u32`
   - Expected: sp.age_add equals `0u32`
   - Expected: sp.max_early_data_size equals `0u32`
   - Expected: _bytes_eq(sp.resumption_secret, psk) is true
   - Expected: _bytes_eq(sp.ticket, ident) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: StoredPsk constructor for external PSK initializes ticket fields")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val psk = _seq_n(32u64, 0x88u8)
val ident = _seq_n(10u64, 0x99u8)
val sp = stored_psk_from_external(psk, ident, 0x1301u16)
expect(sp.cipher_suite).to_equal(0x1301u16)
expect(sp.lifetime_seconds).to_equal(0u32)
expect(sp.age_add).to_equal(0u32)
expect(sp.max_early_data_size).to_equal(0u32)
expect(_bytes_eq(sp.resumption_secret, psk)).to_equal(true)
expect(_bytes_eq(sp.ticket, ident)).to_equal(true)
```

</details>

#### decode_psk_identity advances bytes_consumed correctly

- Verify: decode_psk_identity advances bytes_consumed correctly
   - Expected: d.ok is true
   - Expected: d.bytes_consumed equals `13u64)  # 2 + 7 + 4`
   - Expected: d.id.obfuscated_ticket_age equals `42u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_0RTT-001
step("Verify: decode_psk_identity advances bytes_consumed correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val id = PskIdentity(identity: _seq_n(7u64, 0x33u8), obfuscated_ticket_age: 42u32)
val enc = encode_psk_identity(id)
val d = decode_psk_identity(enc, 0u64)
expect(d.ok).to_equal(true)
expect(d.bytes_consumed).to_equal(13u64)  # 2 + 7 + 4
expect(d.id.obfuscated_ticket_age).to_equal(42u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e1c981e4311cc44176531e4b548665ec560cd07ff751ad9de844cc9e42e2c9b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1c981e4311cc44176531e4b548665ec560cd07ff751ad9de844cc9e42e2c9b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1c981e4311cc44176531e4b548665ec560cd07ff751ad9de844cc9e42e2c9b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/tls13/psk_0rtt_spec.spl
mirror: doc/06_spec/01_unit/os/tls13/psk_0rtt_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tls13/psk_0rtt_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/tls13/psk_0rtt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tls13/psk_0rtt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
