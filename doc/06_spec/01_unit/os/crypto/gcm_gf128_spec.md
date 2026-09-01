# Gcm Gf128 Specification

> Tests covering gcm_gf128_mul / gcm_ghash — shared GCM helper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gcm Gf128 Specification

## Scenarios

### gcm_gf128_mul / gcm_ghash — shared GCM helper

#### x * 0 = 0 for any x (identity of GF(2^128) zero element)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- x * 0 = 0 for any x (identity of GF(2^128) zero element)
   - Expected: product[i] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("x * 0 = 0 for any x (identity of GF(2^128) zero element)")
val product = gcm_gf128_mul(_h_tc1(), _zeros16())
var i: u64 = 0
while i < 16:
    expect(product[i]).to_equal(0x00)
    i = i + 1
```

</details>

#### gcm_pad_to_16 is a no-op on already-16-byte-aligned input

- gcm_pad_to_16 is a no-op on already-16-byte-aligned input
   - Expected: padded.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("gcm_pad_to_16 is a no-op on already-16-byte-aligned input")
val padded = gcm_pad_to_16(_zeros16())
expect(padded.len()).to_equal(16)
```

</details>

#### gcm_pad_to_16 zero-pads a 1-byte input up to 16 bytes

- gcm_pad_to_16 zero-pads a 1-byte input up to 16 bytes
   - Expected: padded.len() equals `16`
   - Expected: padded[0] equals `0xAB`
   - Expected: padded[15] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("gcm_pad_to_16 zero-pads a 1-byte input up to 16 bytes")
var one: [u8] = []
one.push(0xAB)
val padded = gcm_pad_to_16(one)
expect(padded.len()).to_equal(16)
expect(padded[0]).to_equal(0xAB)
expect(padded[15]).to_equal(0x00)
```

</details>

#### gcm_ghash_block(H, 0, 0) = 0 (XOR of zero blocks times H is zero)

- gcm_ghash_block(H, 0, 0) = 0 (XOR of zero blocks times H is zero)
   - Expected: block[i] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("gcm_ghash_block(H, 0, 0) = 0 (XOR of zero blocks times H is zero)")
val block = gcm_ghash_block(_h_tc1(), _zeros16(), _zeros16())
var i: u64 = 0
while i < 16:
    expect(block[i]).to_equal(0x00)
    i = i + 1
```

</details>

#### gcm_ghash(H, empty, empty) matches NIST GCM Test Case 1 GHASH result

- gcm_ghash(H, empty, empty) matches NIST GCM Test Case 1 GHASH result
   - Expected: tag[i] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("gcm_ghash(H, empty, empty) matches NIST GCM Test Case 1 GHASH result")
var empty: [u8] = []
val tag = gcm_ghash(_h_tc1(), empty, empty)
# Only the trailing all-zero length block is hashed: GHASH_H(0^128) = 0.
var i: u64 = 0
while i < 16:
    expect(tag[i]).to_equal(0x00)
    i = i + 1
```

</details>

#### H * 1 = H (GCM's field identity is 0x80 00..00 — pins MSB-first bit order)

- H * 1 = H (GCM's field identity is 0x80 00..00 — pins MSB-first bit order)
   - Expected: product[i] equals `h[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("H * 1 = H (GCM's field identity is 0x80 00..00 — pins MSB-first bit order)")
var one: [u8] = []
one.push(0x80)
var i: u64 = 1
while i < 16:
    one.push(0x00)
    i = i + 1
val product = gcm_gf128_mul(_h_tc1(), one)
val h = _h_tc1()
i = 0
while i < 16:
    expect(product[i]).to_equal(h[i])
    i = i + 1
```

</details>

#### H * x = H>>1 (pins the x^128+x^7+x^2+x+1 reduction, R = 0xE1)

- H * x = H>>1 (pins the x^128+x^7+x^2+x+1 reduction, R = 0xE1)
   - Expected: product[i] equals `expected[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("H * x = H>>1 (pins the x^128+x^7+x^2+x+1 reduction, R = 0xE1)")
# x is 0x40 00..00 in GCM's bit-reflected representation. H's least
# significant bit is 0 (last byte 0x2e), so no reduction fires and the
# product is exactly H shifted right one bit across all 128 bits.
var xe: [u8] = []
xe.push(0x40)
var i: u64 = 1
while i < 16:
    xe.push(0x00)
    i = i + 1
var expected: [u8] = []
expected.push(0x33); expected.push(0x74); expected.push(0xa5); expected.push(0xea)
expected.push(0x77); expected.push(0xc5); expected.push(0x16); expected.push(0x1d)
expected.push(0xc4); expected.push(0x26); expected.push(0x7d); expected.push(0x2c)
expected.push(0xe5); expected.push(0x1a); expected.push(0x15); expected.push(0x97)
val product = gcm_gf128_mul(_h_tc1(), xe)
i = 0
while i < 16:
    expect(product[i]).to_equal(expected[i])
    i = i + 1
```

</details>

#### GHASH(H, empty AAD, TC2 ciphertext) = f38cbb1ad69223dcc3457ae5b6b0f885

- GHASH(H, empty AAD, TC2 ciphertext) = f38cbb1ad69223dcc3457ae5b6b0f885
   - Expected: tag[i] equals `expected[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("GHASH(H, empty AAD, TC2 ciphertext) = f38cbb1ad69223dcc3457ae5b6b0f885")
# NIST SP 800-38D Test Case 2: key = 0^128, IV = 0^96, P = 0^128,
# C = 0388dace60b6a392f328c2b971b2fe78, published Tag =
# ab6e47d42cec13bdf53a67b21257bddf. Since Tag = GHASH XOR E_K(J0) and
# E_K(J0) is the published TC1 tag 58e2fccefa7e3061367f1d57a4e7455a,
# GHASH must equal their XOR, f38cbb1ad69223dcc3457ae5b6b0f885.
var ct: [u8] = []
ct.push(0x03); ct.push(0x88); ct.push(0xda); ct.push(0xce)
ct.push(0x60); ct.push(0xb6); ct.push(0xa3); ct.push(0x92)
ct.push(0xf3); ct.push(0x28); ct.push(0xc2); ct.push(0xb9)
ct.push(0x71); ct.push(0xb2); ct.push(0xfe); ct.push(0x78)
var expected: [u8] = []
expected.push(0xf3); expected.push(0x8c); expected.push(0xbb); expected.push(0x1a)
expected.push(0xd6); expected.push(0x92); expected.push(0x23); expected.push(0xdc)
expected.push(0xc3); expected.push(0x45); expected.push(0x7a); expected.push(0xe5)
expected.push(0xb6); expected.push(0xb0); expected.push(0xf8); expected.push(0x85)
var empty: [u8] = []
val tag = gcm_ghash(_h_tc1(), empty, ct)
var i: u64 = 0
while i < 16:
    expect(tag[i]).to_equal(expected[i])
    i = i + 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/gcm_gf128_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gcm_gf128_mul / gcm_ghash — shared GCM helper.
- gcm_gf128_mul / gcm_ghash — shared GCM helper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a80c896f8fca09e8780c96f6929d36d808aeb630d1011f86dd8c68b7f0a24a3b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a80c896f8fca09e8780c96f6929d36d808aeb630d1011f86dd8c68b7f0a24a3b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a80c896f8fca09e8780c96f6929d36d808aeb630d1011f86dd8c68b7f0a24a3b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/crypto/gcm_gf128_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/gcm_gf128_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/gcm_gf128_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/gcm_gf128_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/gcm_gf128_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/crypto/gcm_gf128_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x * 0 = 0 for any x (identity of GF(2^128) zero element)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/gcm_gf128_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gcm_pad_to_16 is a no-op on already-16-byte-aligned input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/gcm_gf128_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gcm_pad_to_16 zero-pads a 1-byte input up to 16 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
