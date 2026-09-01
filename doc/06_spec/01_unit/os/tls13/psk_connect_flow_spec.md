# Psk Connect Flow Specification

> Tests covering PSK connect-flow splice — RFC 8446 §4.1.4 + §4.2.11 + §4.2.9.

```sdn id=psk_connect_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

psk_connect_flow_spec -> std
psk_connect_flow_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=psk_connect_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# psk_connect_flow_spec

Verifies the psk connect flow behaviour end to end so maintainers of this

## Scenarios

### PSK connect-flow splice — RFC 8446 §4.1.4 + §4.2.11 + §4.2.9

#### partial-CH binders_field_offset places binders_len after identities

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### pre_shared_key extension is the LAST extension in CH (RFC 8446 §4.2.11)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = _make_psk_config(_seq_n(32u64, 0x11u8), _seq_n(8u64, 0x77u8))
val ch_base = build_client_hello_bytes(_ch_random32(), _x25519_pub32(), "example.com")
val psk_ch = _splice_psk_extensions_into_ch(ch_base, cfg)
# The last extension must start with type 0x00 0x29 (pre_shared_key).
# Walk back from end: the binders block sits at the tail. The whole
# pre_shared_key extension starts at psk_ch.binders_field_offset - 4 - ids_len_plus_2.
# Simpler: the binders_data_offset + binder_len(33) should equal wire.len().
val expected_end = psk_ch.binders_data_offset + 33u64
expect(expected_end).to_equal(psk_ch.bytes.len().to_u64())
```

</details>

#### psk_key_exchange_modes extension (type 0x002d) is present in CH

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = _make_psk_config(_seq_n(32u64, 0x11u8), _seq_n(8u64, 0x77u8))
val ch_base = build_client_hello_bytes(_ch_random32(), _x25519_pub32(), "example.com")
val psk_ch = _splice_psk_extensions_into_ch(ch_base, cfg)
# Module-level helper to keep the scan loop out of the it-block
# (interpreter doesn't persist var mutations across while iterations
# inside it-blocks; see feedback_it_block_var_mutation.md).
val found = _scan_for_ext_type(psk_ch.bytes, 0x00, 0x2d)
expect(found).to_equal(true)
```

</details>

#### partial-CH transcript hash stops at end of identities (RFC 8446 §4.1.4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The hash STOPS at binders_field_offset, NOT at end of zeroed binders.
# _partial_ch_transcript_hash must equal SHA-256(wire[0..binders_field_offset]).
val cfg = _make_psk_config(_seq_n(32u64, 0x11u8), _seq_n(8u64, 0x77u8))
val ch_base = build_client_hello_bytes(_ch_random32(), _x25519_pub32(), "example.com")
val psk_ch = _splice_psk_extensions_into_ch(ch_base, cfg)
val got = _partial_ch_transcript_hash(psk_ch.bytes, psk_ch, 1u8)
# Independent SHA-256 over the same prefix using a module-level helper
# to keep the prefix-build loop out of the it-block.
val prefix = _build_prefix_to(psk_ch.bytes, psk_ch.binders_field_offset)
val expected = rt_tls13_sha256(prefix)
expect(got.len()).to_equal(32)
expect(_bytes_eq(got, expected)).to_equal(true)
```

</details>

#### partial-CH transcript hash is NOT the same as hashing including zero binders

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Negative check: hashing [0..end_of_binders] would produce a DIFFERENT
# digest than [0..binders_field_offset]. RFC 8446 §4.1.4 mandates the
# latter; this guards against the silent wrong interpretation.
val cfg = _make_psk_config(_seq_n(32u64, 0x11u8), _seq_n(8u64, 0x77u8))
val ch_base = build_client_hello_bytes(_ch_random32(), _x25519_pub32(), "example.com")
val psk_ch = _splice_psk_extensions_into_ch(ch_base, cfg)
val got = _partial_ch_transcript_hash(psk_ch.bytes, psk_ch, 1u8)
# Hash including the binders block (binders_len + zeroed binders).
var full: [u8] = []
var i: u64 = 0
val end = psk_ch.bytes.len().to_u64()
while i < end:
    full = _pb(full, rt_bytes_u8_at(psk_ch.bytes, i.to_i64()))
    i = i + 1
val full_hash = rt_tls13_sha256(full)
expect(_bytes_eq(got, full_hash)).to_equal(false)
```

</details>

#### spliced binder MAC matches tls13_compute_psk_binder byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Compute binder via the same path as tls13_connect_io_with_config and
# verify the spliced wire bytes contain exactly that MAC.
val psk_secret = _seq_n(32u64, 0x11u8)
val cfg = _make_psk_config(psk_secret, _seq_n(8u64, 0x77u8))
val ch_base = build_client_hello_bytes(_ch_random32(), _x25519_pub32(), "example.com")
val psk_ch = _splice_psk_extensions_into_ch(ch_base, cfg)
val partial_th = _partial_ch_transcript_hash(psk_ch.bytes, psk_ch, 1u8)
val es = tls13_early_secret_from_psk(psk_secret, 1u8)
val bk = tls13_binder_key(es, 1u8, true)
val mac = tls13_compute_psk_binder(bk, partial_th, 1u8)
var binders: [[u8]] = []
binders.push(mac)
val spliced = _splice_binder_bytes(psk_ch.bytes, psk_ch, binders)
# Verify byte-exact: bytes[binders_data_offset+1 ..+33] == mac.
var ok = true
var i: u64 = 0
while i < 32:
    val abs_off = psk_ch.binders_data_offset + 1u64 + i
    if _u8_get(spliced, abs_off) != _u8_get(mac, i):
        ok = false
    i = i + 1
expect(ok).to_equal(true)
# Length unchanged after splice.
expect(spliced.len()).to_equal(psk_ch.bytes.len())
```

</details>

#### ServerHello with pre_shared_key selected_identity=0 returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = _build_sh_body_with_psk(0u16)
val sel = _parse_sh_selected_identity(body)
expect(sel).to_equal(0)
```

</details>

#### ServerHello without pre_shared_key returns -1 (no PSK selected)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = _build_sh_body_no_psk()
val sel = _parse_sh_selected_identity(body)
expect(sel).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/psk_connect_flow_spec.spl` |
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

- Canonical SPipe generation for source `70a343f9dbd324ae6fa2c8696be93c632423793f3383cd664f25107c9b513f9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70a343f9dbd324ae6fa2c8696be93c632423793f3383cd664f25107c9b513f9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70a343f9dbd324ae6fa2c8696be93c632423793f3383cd664f25107c9b513f9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/os/tls13/psk_connect_flow_spec.spl
mirror: doc/06_spec/01_unit/os/tls13/psk_connect_flow_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tls13/psk_connect_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tls13/psk_connect_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tls13/psk_connect_flow_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/tls13/psk_connect_flow_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tls13/psk_connect_flow_spec.spl:194:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'partial-CH binders_field_offset places binders_len after identities' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/tls13/psk_connect_flow_spec.spl:215:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'pre_shared_key extension is the LAST extension in CH (RFC 8446 §4.2.11)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/tls13/psk_connect_flow_spec.spl:226:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'psk_key_exchange_modes extension (type 0x002d) is present in CH' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/tls13/psk_connect_flow_spec.spl:236:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'partial-CH transcript hash stops at end of identities (RFC 8446 §4.1.4)' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
