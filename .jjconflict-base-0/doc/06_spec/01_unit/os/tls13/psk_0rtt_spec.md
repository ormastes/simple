# Psk 0rtt Specification

> Tests covering PSK + 0-RTT — RFC 8446 §4.2.11 + §4.2.10 + §7.1.

```sdn id=psk_0rtt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

psk_0rtt_spec -> std
psk_0rtt_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=psk_0rtt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# psk_0rtt_spec

Verifies the psk 0rtt behaviour end to end so maintainers of this

## Scenarios

### PSK + 0-RTT — RFC 8446 §4.2.11 + §4.2.10 + §7.1

#### PskIdentity wire encoding length: 2 + id_len + 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### PskBinder wire encoding has 1-byte length prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = PskBinder(binder: _seq_n(32u64, 0xCCu8))
val out = encode_psk_binder(b)
expect(out.len()).to_equal(33)
expect(out[0].to_u32()).to_equal(32u32)
expect(out[1].to_u32()).to_equal(0xCCu32)
expect(out[32].to_u32()).to_equal(0xCCu32)
```

</details>

#### OfferedPsks encode produces both identity and binder length frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offer = _build_simple_offer()
val out = encode_offered_psk(offer)
# identities block:  uint16 len + (uint16 id_len + 8 + 4) = 2 + 14 = 16
# binders block:     uint16 len + (uint8 + 32) = 2 + 33 = 35
# total = 16 + 35 = 51
expect(out.len()).to_equal(51)
# outer identities length = 14
expect(_u16_be(out, 0u64)).to_equal(14u32)
# binders length frame at offset 16 = 33
expect(_u16_be(out, 16u64)).to_equal(33u32)
```

</details>

#### OfferedPsks encode round-trips through decode

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offer = _build_simple_offer()
val out = encode_offered_psk(offer)
val d = decode_offered_psk(out)
expect(d.ok).to_equal(true)
expect(d.psk.identities.len()).to_equal(1)
expect(d.psk.binders.len()).to_equal(1)
val got_id = d.psk.identities[0]
expect(got_id.obfuscated_ticket_age).to_equal(0xDEADBEEFu32)
expect(_bytes_eq(got_id.identity, _seq_n(8u64, 0x10u8))).to_equal(true)
val got_binder = d.psk.binders[0]
expect(_bytes_eq(got_binder.binder, _seq_n(32u64, 0x20u8))).to_equal(true)
```

</details>

#### decode_offered_psk rejects truncated input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short_input: [u8] = [0x00u8, 0x05u8]  # claims 5 bytes of identities, none follow
val d = decode_offered_psk(short_input)
expect(d.ok).to_equal(false)
```

</details>

#### decode_offered_psk rejects binder shorter than 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ident = _seq_n(4u64, 0x44u8)
val ids: [PskIdentity] = [PskIdentity(identity: ident, obfuscated_ticket_age: 0u32)]
val lens: [u32] = [32u32]
val out = encode_offered_psk_partial(ids, lens)
# identities block: 2 (id_len) + 4 + 4 = 10  → ids_len=10 → outer 12
# binders block: 1 + 32 = 33  → 2 + 33 = 35
# total = 12 + 35 = 47
expect(out.len()).to_equal(47)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero32 = _zeros32()
val es = tls13_early_secret_from_psk(zero32, 1u8)
# Reference: HKDF-Extract(salt=0^32, IKM=0^32) — matches the all-zero
# PSK case which equals tls13_early_secret() result.
val ref_es = hkdf_extract(zero32, zero32)
# ref_es may be longer; compare first 32 bytes
expect(es.len()).to_equal(32)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero32 = _zeros32()
val es = tls13_early_secret_from_psk(zero32, 1u8)
val bk_ext = tls13_binder_key(es, 1u8, false)
val bk_res = tls13_binder_key(es, 1u8, true)
expect(bk_ext.len()).to_equal(32)
expect(bk_res.len()).to_equal(32)
# ext binder ≠ res binder
expect(_bytes_eq(bk_ext, bk_res)).to_equal(false)
```

</details>

#### psk binder MAC = HMAC-SHA-256(finished_key, transcript_hash)

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(got_mac.len()).to_equal(32)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero32 = _zeros32()
val es = tls13_early_secret_from_psk(zero32, 1u8)
val th = _seq_n(32u64, 0x77u8)
val cets = tls13_client_early_traffic_secret(es, th, 1u8)
expect(cets.len()).to_equal(32)
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = PskIdentity(identity: _seq_n(7u64, 0x33u8), obfuscated_ticket_age: 42u32)
val enc = encode_psk_identity(id)
val d = decode_psk_identity(enc, 0u64)
expect(d.ok).to_equal(true)
expect(d.bytes_consumed).to_equal(13u64)  # 2 + 7 + 4
expect(d.id.obfuscated_ticket_age).to_equal(42u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/psk_0rtt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d27bb9326ee93383cd29b694a78fe30a691269434f827e554fa4d0ce8b11c2c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d27bb9326ee93383cd29b694a78fe30a691269434f827e554fa4d0ce8b11c2c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d27bb9326ee93383cd29b694a78fe30a691269434f827e554fa4d0ce8b11c2c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/os/tls13/psk_0rtt_spec.spl
mirror: doc/06_spec/01_unit/os/tls13/psk_0rtt_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tls13/psk_0rtt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tls13/psk_0rtt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tls13/psk_0rtt_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/tls13/psk_0rtt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tls13/psk_0rtt_spec.spl:87:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'PskIdentity wire encoding length: 2 + id_len + 4' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/tls13/psk_0rtt_spec.spl:103:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'PskBinder wire encoding has 1-byte length prefix' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/tls13/psk_0rtt_spec.spl:111:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'OfferedPsks encode produces both identity and binder length frames' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/tls13/psk_0rtt_spec.spl:123:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'OfferedPsks encode round-trips through decode' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
