# Salsa20 Specification

> Tests covering Salsa20/20 block — DJB spec Set 1 vector 0 (key=0x80..0, nonce=0), Salsa20/20 block — DJB spec Set 2 vector 0 (key=0, nonce=0x80..0), Salsa20/20 block — DJB spec Set 0 vector 0 (all-zero key+nonce), Salsa20/20 XOR — round-trip and length, HSalsa20 — NaCl reference vector (DJB crypto_core/hsalsa20/ref/test.c), XSalsa20 — computed byte-exact vector (Python-verified), XSalsa20 — round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Salsa20 Specification

## Scenarios

### Salsa20/20 block — DJB spec Set 1 vector 0 (key=0x80..0, nonce=0)

#### block output is 64 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- block output is 64 bytes
   - Expected: out.len() equals `64u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block output is 64 bytes")
val out = salsa20_20_block(_make_key_0x80(), _make_nonce_zeros_8(), 0u32, 0u32)
expect(out.len()).to_equal(64u64)
```

</details>

#### block output matches DJB spec byte-exact

- block output matches DJB spec byte-exact
   - Expected: _bytes_hex(out) equals `_bytes_hex(_expected_set1_v0())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block output matches DJB spec byte-exact")
val out = salsa20_20_block(_make_key_0x80(), _make_nonce_zeros_8(), 0u32, 0u32)
expect(_bytes_hex(out)).to_equal(_bytes_hex(_expected_set1_v0()))
```

</details>

### Salsa20/20 block — DJB spec Set 2 vector 0 (key=0, nonce=0x80..0)

#### block output is 64 bytes

- block output is 64 bytes
   - Expected: out.len() equals `64u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block output is 64 bytes")
val out = salsa20_20_block(_make_key_zeros(), _make_nonce_0x80(), 0u32, 0u32)
expect(out.len()).to_equal(64u64)
```

</details>

#### block output matches DJB spec byte-exact

- block output matches DJB spec byte-exact
   - Expected: _bytes_hex(out) equals `_bytes_hex(_expected_set2_v0())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block output matches DJB spec byte-exact")
val out = salsa20_20_block(_make_key_zeros(), _make_nonce_0x80(), 0u32, 0u32)
expect(_bytes_hex(out)).to_equal(_bytes_hex(_expected_set2_v0()))
```

</details>

### Salsa20/20 block — DJB spec Set 0 vector 0 (all-zero key+nonce)

#### block output matches DJB spec byte-exact

- block output matches DJB spec byte-exact
   - Expected: _bytes_hex(out) equals `_bytes_hex(_expected_set0_v0())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block output matches DJB spec byte-exact")
val out = salsa20_20_block(_make_key_zeros(), _make_nonce_zeros_8(), 0u32, 0u32)
expect(_bytes_hex(out)).to_equal(_bytes_hex(_expected_set0_v0()))
```

</details>

### Salsa20/20 XOR — round-trip and length

#### output length equals plaintext length

- output length equals plaintext length
   - Expected: ct.len() equals `8u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output length equals plaintext length")
val pt: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8]
val ct = salsa20_20_xor(_make_key_0x80(), _make_nonce_zeros_8(), pt)
expect(ct.len()).to_equal(8u64)
```

</details>

#### encrypt then decrypt recovers original plaintext

- encrypt then decrypt recovers original plaintext
   - Expected: _bytes_hex(rt) equals `_bytes_hex(pt)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt then decrypt recovers original plaintext")
val pt: [u8] = [
    0x01u8, 0x23u8, 0x45u8, 0x67u8, 0x89u8, 0xabu8, 0xcdu8, 0xefu8,
    0xfeu8, 0xdcu8, 0xbau8, 0x98u8, 0x76u8, 0x54u8, 0x32u8, 0x10u8
]
val ct = salsa20_20_xor(_make_key_0x80(), _make_nonce_zeros_8(), pt)
val rt = salsa20_20_xor(_make_key_0x80(), _make_nonce_zeros_8(), ct)
expect(_bytes_hex(rt)).to_equal(_bytes_hex(pt))
```

</details>

### HSalsa20 — NaCl reference vector (DJB crypto_core/hsalsa20/ref/test.c)

#### output is 32 bytes

- output is 32 bytes
   - Expected: out.len() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output is 32 bytes")
val out = hsalsa20(_hsalsa_key(), _hsalsa_input())
expect(out.len()).to_equal(32u64)
```

</details>

#### output matches NaCl reference vector byte-exact

- output matches NaCl reference vector byte-exact
   - Expected: _bytes_hex(out) equals `_bytes_hex(_hsalsa_expected())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output matches NaCl reference vector byte-exact")
val out = hsalsa20(_hsalsa_key(), _hsalsa_input())
expect(_bytes_hex(out)).to_equal(_bytes_hex(_hsalsa_expected()))
```

</details>

### XSalsa20 — computed byte-exact vector (Python-verified)

#### output length equals plaintext length (35 bytes)

- output length equals plaintext length (35 bytes)
   - Expected: ct.len() equals `35u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output length equals plaintext length (35 bytes)")
val ct = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), _xsalsa_plaintext())
expect(ct.len()).to_equal(35u64)
```

</details>

#### encryption matches computed ciphertext byte-exact

- encryption matches computed ciphertext byte-exact
   - Expected: _bytes_hex(ct) equals `_bytes_hex(_xsalsa_expected_ct())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encryption matches computed ciphertext byte-exact")
val ct = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), _xsalsa_plaintext())
expect(_bytes_hex(ct)).to_equal(_bytes_hex(_xsalsa_expected_ct()))
```

</details>

### XSalsa20 — round-trip

#### encrypt then decrypt recovers original plaintext

- encrypt then decrypt recovers original plaintext
   - Expected: _bytes_hex(rt) equals `_bytes_hex(pt)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypt then decrypt recovers original plaintext")
val pt = _xsalsa_plaintext()
val ct = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), pt)
val rt = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), ct)
expect(_bytes_hex(rt)).to_equal(_bytes_hex(pt))
```

</details>

#### different keys produce different ciphertext

- different keys produce different ciphertext


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different keys produce different ciphertext")
val pt = _xsalsa_plaintext()
val ct1 = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), pt)
val ct2 = xsalsa20_xor(_make_key_zeros(), _xsalsa_nonce24(), pt)
assert_not_equal(_bytes_hex(ct1), _bytes_hex(ct2))
```

</details>

#### different nonces produce different ciphertext

- different nonces produce different ciphertext


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different nonces produce different ciphertext")
val pt = _xsalsa_plaintext()
val ct1 = xsalsa20_xor(_hsalsa_key(), _xsalsa_nonce24(), pt)
val ct2 = xsalsa20_xor(_hsalsa_key(), _nonce24_alt(), pt)
assert_not_equal(_bytes_hex(ct1), _bytes_hex(ct2))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/salsa20_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Salsa20/20 block — DJB spec Set 1 vector 0 (key=0x80..0, nonce=0), Salsa20/20 block — DJB spec Set 2 vector 0 (key=0, nonce=0x80..0), Salsa20/20 block — DJB spec Set 0 vector 0 (all-zero key+nonce), Salsa20/20 XOR — round-trip and length, HSalsa20 — NaCl reference vector (DJB crypto_core/hsalsa20/ref/test.c), XSalsa20 — computed byte-exact vector (Python-verified), XSalsa20 — round-trip.
- Salsa20/20 block — DJB spec Set 1 vector 0 (key=0x80..0, nonce=0)
- Salsa20/20 block — DJB spec Set 2 vector 0 (key=0, nonce=0x80..0)
- Salsa20/20 block — DJB spec Set 0 vector 0 (all-zero key+nonce)
- Salsa20/20 XOR — round-trip and length
- HSalsa20 — NaCl reference vector (DJB crypto_core/hsalsa20/ref/test.c)
- XSalsa20 — computed byte-exact vector (Python-verified)
- XSalsa20 — round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `0634efe45f05d2770f3cfc3ecc65add9118f063098241cd06690d867b408a5e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0634efe45f05d2770f3cfc3ecc65add9118f063098241cd06690d867b408a5e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0634efe45f05d2770f3cfc3ecc65add9118f063098241cd06690d867b408a5e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/salsa20_spec.spl
mirror: doc/06_spec/unit/lib/crypto/salsa20_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/salsa20_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/salsa20_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/salsa20_spec.spl:234:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'block output is 64 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/salsa20_spec.spl:240:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'block output matches DJB spec byte-exact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/salsa20_spec.spl:248:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'block output is 64 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
