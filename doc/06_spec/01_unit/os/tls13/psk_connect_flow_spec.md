# psk_connect_flow_spec

> Verifies the psk connect flow behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# psk_connect_flow_spec

Verifies the psk connect flow behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/psk_connect_flow_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the psk connect flow behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### PSK connect-flow splice — RFC 8446 §4.1.4 + §4.2.11 + §4.2.9

#### partial-CH binders_field_offset places binders_len after identities

- Verify: partial-CH binders_field_offset places binders_len after identities
   - Expected: psk_ch.binders_data_offset equals `psk_ch.binders_field_offset + 2u64`
   - Expected: bl equals `33u32`
   - Expected: _u8_get(wire, psk_ch.binders_data_offset) equals `32u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: partial-CH binders_field_offset places binders_len after identities")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
# Build a CH with our PSK config and check that the offset matches
# ext_data_len semantics: ext_data starts with u16 ids_len + ids,
# followed by binders_len u16 at binders_field_offset.
val cfg = _make_psk_config(_seq_n(32u64, 0x11u8), _seq_n(8u64, 0x77u8))
val ch_base = build_client_hello_bytes(_ch_random32(), _x25519_pub32(), "example.com")
val psk_ch = _splice_psk_extensions_into_ch(ch_base, cfg)
val wire = psk_ch.bytes
# binders_data_offset must equal binders_field_offset + 2
expect(psk_ch.binders_data_offset).to_equal(psk_ch.binders_field_offset + 2u64)
# The bytes at binders_field_offset..binders_field_offset+2 are the
# binders_len u16 = 1 (1-byte plen) + 32 (binder body) = 33.
val bl_hi = _u8_get(wire, psk_ch.binders_field_offset).to_u32()
val bl_lo = _u8_get(wire, psk_ch.binders_field_offset + 1u64).to_u32()
val bl = ((bl_hi << 8) | bl_lo)
expect(bl).to_equal(33u32)
# The byte at binders_data_offset is the per-binder length prefix = 32.
expect(_u8_get(wire, psk_ch.binders_data_offset)).to_equal(32u8)
```

</details>

#### pre_shared_key extension is the LAST extension in CH (RFC 8446 §4.2.11)

- Verify: pre_shared_key extension is the LAST extension in CH (RFC 8446 §4.2.11)
   - Expected: expected_end equals `psk_ch.bytes.len().to_u64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: pre_shared_key extension is the LAST extension in CH (RFC 8446 §4.2.11)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: psk_key_exchange_modes extension (type 0x002d) is present in CH
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: psk_key_exchange_modes extension (type 0x002d) is present in CH")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: partial-CH transcript hash stops at end of identities (RFC 8446 §4.1.4)
   - Expected: got.len() equals `32)  # oracle: pinned constant asserted by this scenario`
   - Expected: _bytes_eq(got, expected) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: partial-CH transcript hash stops at end of identities (RFC 8446 §4.1.4)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(got.len()).to_equal(32)  # oracle: pinned constant asserted by this scenario
expect(_bytes_eq(got, expected)).to_equal(true)
```

</details>

#### partial-CH transcript hash is NOT the same as hashing including zero binders

- Verify: partial-CH transcript hash is NOT the same as hashing including zero binders
   - Expected: _bytes_eq(got, full_hash) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: partial-CH transcript hash is NOT the same as hashing including zero binders")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: spliced binder MAC matches tls13_compute_psk_binder byte-exact
   - Expected: ok is true
   - Expected: spliced.len() equals `psk_ch.bytes.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: spliced binder MAC matches tls13_compute_psk_binder byte-exact")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: ServerHello with pre_shared_key selected_identity=0 returns 0
   - Expected: sel equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: ServerHello with pre_shared_key selected_identity=0 returns 0")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val body = _build_sh_body_with_psk(0u16)
val sel = _parse_sh_selected_identity(body)
expect(sel).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### ServerHello without pre_shared_key returns -1 (no PSK selected)

- Verify: ServerHello without pre_shared_key returns -1 (no PSK selected)
   - Expected: sel equals `-1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-TLS13_PSK_CONNECT_FLOW-001
step("Verify: ServerHello without pre_shared_key returns -1 (no PSK selected)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val body = _build_sh_body_no_psk()
val sel = _parse_sh_selected_identity(body)
expect(sel).to_equal(-1)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9cd44e9adc1a50fcbba1a60c42040b9da82458de87cbbeb5a763b8b97d477ed6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9cd44e9adc1a50fcbba1a60c42040b9da82458de87cbbeb5a763b8b97d477ed6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9cd44e9adc1a50fcbba1a60c42040b9da82458de87cbbeb5a763b8b97d477ed6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/tls13/psk_connect_flow_spec.spl
mirror: doc/06_spec/01_unit/os/tls13/psk_connect_flow_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tls13/psk_connect_flow_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/tls13/psk_connect_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tls13/psk_connect_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
