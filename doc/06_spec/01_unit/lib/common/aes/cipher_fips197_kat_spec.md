# Cipher Fips197 Kat Specification

> Tests covering AES-128 key expansion — FIPS 197 Appendix A.1, AES-256 key expansion — FIPS 197 Appendix A.3, AES block cipher — FIPS 197 Appendix C.1 (AES-128), AES block cipher — FIPS 197 Appendix C.3 (AES-256).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cipher Fips197 Kat Specification

## Scenarios

### AES-128 key expansion — FIPS 197 Appendix A.1

#### produces round key 0 equal to the cipher key itself

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces round key 0 equal to the cipher key itself
   - Expected: get_round_key(w, 0) equals `_a1_key()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces round key 0 equal to the cipher key itself")
val w = expand_key(_a1_key(), 16)
expect(get_round_key(w, 0)).to_equal(_a1_key())
```

</details>

#### produces the published w4..w7 (round key 1)

- produces the published w4..w7 (round key 1)
   - Expected: get_key_word(w, 4) equals `[0xa0, 0xfa, 0xfe, 0x17]`
   - Expected: get_key_word(w, 5) equals `[0x88, 0x54, 0x2c, 0xb1]`
   - Expected: get_key_word(w, 6) equals `[0x23, 0xa3, 0x39, 0x39]`
   - Expected: get_key_word(w, 7) equals `[0x2a, 0x6c, 0x76, 0x05]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the published w4..w7 (round key 1)")
# A.1: w4=a0fafe17 w5=88542cb1 w6=23a33939 w7=2a6c7605
# This is the assertion a round-trip test can never make. It is also
# the one that catches a RotWord/SubWord ordering swap or an rcon[1]
# off-by-one.
val w = expand_key(_a1_key(), 16)
expect(get_key_word(w, 4)).to_equal([0xa0, 0xfa, 0xfe, 0x17])
expect(get_key_word(w, 5)).to_equal([0x88, 0x54, 0x2c, 0xb1])
expect(get_key_word(w, 6)).to_equal([0x23, 0xa3, 0x39, 0x39])
expect(get_key_word(w, 7)).to_equal([0x2a, 0x6c, 0x76, 0x05])
```

</details>

#### produces the published round key 1 as a contiguous 16-byte slice

- produces the published round key 1 as a contiguous 16-byte slice


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the published round key 1 as a contiguous 16-byte slice")
val w = expand_key(_a1_key(), 16)
expect(get_round_key(w, 1)).to_equal(
    [0xa0, 0xfa, 0xfe, 0x17, 0x88, 0x54, 0x2c, 0xb1,
     0x23, 0xa3, 0x39, 0x39, 0x2a, 0x6c, 0x76, 0x05])
```

</details>

#### produces the published w36..w39 (round key 9, exercises rcon[9]=0x1b)

- produces the published w36..w39 (round key 9, exercises rcon[9]=0x1b)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the published w36..w39 (round key 9, exercises rcon[9]=0x1b)")
# rcon[9] = 0x1b is where the round constant stops being a plain
# power of two. Asserting only w4 cannot catch a corrupt entry here.
val w = expand_key(_a1_key(), 16)
expect(get_round_key(w, 9)).to_equal(
    [0xac, 0x77, 0x66, 0xf3, 0x19, 0xfa, 0xdc, 0x21,
     0x28, 0xd1, 0x29, 0x41, 0x57, 0x5c, 0x00, 0x6e])
```

</details>

#### produces the published final round key 10 (exercises rcon[10]=0x36)

- produces the published final round key 10 (exercises rcon[10]=0x36)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the published final round key 10 (exercises rcon[10]=0x36)")
# A.1 last line: w40=d014f9a8 w41=c9ee2589 w42=e13f0cc8 w43=b6630ca6
val w = expand_key(_a1_key(), 16)
expect(get_round_key(w, 10)).to_equal(
    [0xd0, 0x14, 0xf9, 0xa8, 0xc9, 0xee, 0x25, 0x89,
     0xe1, 0x3f, 0x0c, 0xc8, 0xb6, 0x63, 0x0c, 0xa6])
```

</details>

#### expands to exactly 11 round keys (176 bytes)

- expands to exactly 11 round keys (176 bytes)
   - Expected: expand_key(_a1_key(), 16).length() equals `176`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands to exactly 11 round keys (176 bytes)")
expect(expand_key(_a1_key(), 16).length()).to_equal(176)
```

</details>

### AES-256 key expansion — FIPS 197 Appendix A.3

#### produces round keys 0 and 1 equal to the two halves of the cipher key

- produces round keys 0 and 1 equal to the two halves of the cipher key


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces round keys 0 and 1 equal to the two halves of the cipher key")
val w = expand_key(_a3_key(), 32)
expect(get_round_key(w, 0)).to_equal(
    [0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe,
     0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81])
expect(get_round_key(w, 1)).to_equal(
    [0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7,
     0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4])
```

</details>

#### produces the published w8..w11 (round key 2)

- produces the published w8..w11 (round key 2)
   - Expected: get_key_word(w, 8) equals `[0x9b, 0xa3, 0x54, 0x11]`
   - Expected: get_key_word(w, 9) equals `[0x8e, 0x69, 0x25, 0xaf]`
   - Expected: get_key_word(w, 10) equals `[0xa5, 0x1a, 0x8b, 0x5f]`
   - Expected: get_key_word(w, 11) equals `[0x20, 0x67, 0xfc, 0xde]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the published w8..w11 (round key 2)")
# A.3: w8=9ba35411 w9=8e6925af w10=a51a8b5f w11=2067fcde
val w = expand_key(_a3_key(), 32)
expect(get_key_word(w, 8)).to_equal([0x9b, 0xa3, 0x54, 0x11])
expect(get_key_word(w, 9)).to_equal([0x8e, 0x69, 0x25, 0xaf])
expect(get_key_word(w, 10)).to_equal([0xa5, 0x1a, 0x8b, 0x5f])
expect(get_key_word(w, 11)).to_equal([0x20, 0x67, 0xfc, 0xde])
```

</details>

#### produces the published w12..w15 (round key 3, the extra SubWord step)

- produces the published w12..w15 (round key 3, the extra SubWord step)
   - Expected: get_key_word(w, 12) equals `[0xa8, 0xb0, 0x9c, 0x1a]`
   - Expected: get_key_word(w, 13) equals `[0x93, 0xd1, 0x94, 0xcd]`
   - Expected: get_key_word(w, 14) equals `[0xbe, 0x49, 0x84, 0x6e]`
   - Expected: get_key_word(w, 15) equals `[0xb7, 0x5d, 0x5b, 0x9a]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the published w12..w15 (round key 3, the extra SubWord step)")
# AES-256 applies an EXTRA SubWord at i % Nk == 4 with no RotWord and
# no rcon. w12..w15 is the first place that branch runs, so this is
# the assertion that catches it being missing, misplaced, or applied
# with a spurious RotWord.
val w = expand_key(_a3_key(), 32)
expect(get_key_word(w, 12)).to_equal([0xa8, 0xb0, 0x9c, 0x1a])
expect(get_key_word(w, 13)).to_equal([0x93, 0xd1, 0x94, 0xcd])
expect(get_key_word(w, 14)).to_equal([0xbe, 0x49, 0x84, 0x6e])
expect(get_key_word(w, 15)).to_equal([0xb7, 0x5d, 0x5b, 0x9a])
```

</details>

#### produces the published final round key 14

- produces the published final round key 14


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces the published final round key 14")
# A.3 last line: w56=fe4890d1 w57=e6188d0b w58=046df344 w59=706c631e
val w = expand_key(_a3_key(), 32)
expect(get_round_key(w, 14)).to_equal(
    [0xfe, 0x48, 0x90, 0xd1, 0xe6, 0x18, 0x8d, 0x0b,
     0x04, 0x6d, 0xf3, 0x44, 0x70, 0x6c, 0x63, 0x1e])
```

</details>

#### expands to exactly 15 round keys (240 bytes)

- expands to exactly 15 round keys (240 bytes)
   - Expected: expand_key(_a3_key(), 32).length() equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands to exactly 15 round keys (240 bytes)")
expect(expand_key(_a3_key(), 32).length()).to_equal(240)
```

</details>

### AES block cipher — FIPS 197 Appendix C.1 (AES-128)

#### encrypts the published plaintext to the published ciphertext

- encrypts the published plaintext to the published ciphertext
   - Expected: aes_encrypt_block(_c_pt(), _c1_key()) equals `_c1_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encrypts the published plaintext to the published ciphertext")
expect(aes_encrypt_block(_c_pt(), _c1_key())).to_equal(_c1_ct())
```

</details>

#### decrypts the published ciphertext back to the published plaintext

- decrypts the published ciphertext back to the published plaintext
   - Expected: aes_decrypt_block(_c1_ct(), _c1_key()) equals `_c_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decrypts the published ciphertext back to the published plaintext")
expect(aes_decrypt_block(_c1_ct(), _c1_key())).to_equal(_c_pt())
```

</details>

#### encrypts identically through the software (scalar) round chain

- encrypts identically through the software (scalar) round chain
   - Expected: _scalar_aes_encrypt_block_with_expanded(_c_pt(), w, 10) equals `_c1_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encrypts identically through the software (scalar) round chain")
# aes_encrypt_block routes to the SIMD chain, leaving the scalar
# encrypt path and its sub_bytes/shift_rows/mix_columns helpers
# untested by the public API. Pin it directly.
val w = expand_key(_c1_key(), 16)
expect(_scalar_aes_encrypt_block_with_expanded(_c_pt(), w, 10)).to_equal(_c1_ct())
```

</details>

#### round-trips through the with_expanded entry points

- round-trips through the with_expanded entry points
   - Expected: ct equals `_c1_ct()`
   - Expected: aes_decrypt_block_with_expanded(ct, w, 10) equals `_c_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips through the with_expanded entry points")
val w = expand_key(_c1_key(), 16)
val ct = aes_encrypt_block_with_expanded(_c_pt(), w, 10)
expect(ct).to_equal(_c1_ct())
expect(aes_decrypt_block_with_expanded(ct, w, 10)).to_equal(_c_pt())
```

</details>

### AES block cipher — FIPS 197 Appendix C.3 (AES-256)

#### encrypts the published plaintext to the published ciphertext

- encrypts the published plaintext to the published ciphertext
   - Expected: aes_encrypt_block(_c_pt(), _c3_key()) equals `_c3_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encrypts the published plaintext to the published ciphertext")
expect(aes_encrypt_block(_c_pt(), _c3_key())).to_equal(_c3_ct())
```

</details>

#### decrypts the published ciphertext back to the published plaintext

- decrypts the published ciphertext back to the published plaintext
   - Expected: aes_decrypt_block(_c3_ct(), _c3_key()) equals `_c_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decrypts the published ciphertext back to the published plaintext")
expect(aes_decrypt_block(_c3_ct(), _c3_key())).to_equal(_c_pt())
```

</details>

#### encrypts identically through the software (scalar) round chain

- encrypts identically through the software (scalar) round chain
   - Expected: _scalar_aes_encrypt_block_with_expanded(_c_pt(), w, 14) equals `_c3_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("encrypts identically through the software (scalar) round chain")
val w = expand_key(_c3_key(), 32)
expect(_scalar_aes_encrypt_block_with_expanded(_c_pt(), w, 14)).to_equal(_c3_ct())
```

</details>

#### round-trips through the with_expanded entry points

- round-trips through the with_expanded entry points
   - Expected: ct equals `_c3_ct()`
   - Expected: aes_decrypt_block_with_expanded(ct, w, 14) equals `_c_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips through the with_expanded entry points")
val w = expand_key(_c3_key(), 32)
val ct = aes_encrypt_block_with_expanded(_c_pt(), w, 14)
expect(ct).to_equal(_c3_ct())
expect(aes_decrypt_block_with_expanded(ct, w, 14)).to_equal(_c_pt())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/aes/cipher_fips197_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-128 key expansion — FIPS 197 Appendix A.1, AES-256 key expansion — FIPS 197 Appendix A.3, AES block cipher — FIPS 197 Appendix C.1 (AES-128), AES block cipher — FIPS 197 Appendix C.3 (AES-256).
- AES-128 key expansion — FIPS 197 Appendix A.1
- AES-256 key expansion — FIPS 197 Appendix A.3
- AES block cipher — FIPS 197 Appendix C.1 (AES-128)
- AES block cipher — FIPS 197 Appendix C.3 (AES-256)

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5807e4af6cf40f283a2b331f80804838fd58d4466c00309765372dfdcf2d2b1f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5807e4af6cf40f283a2b331f80804838fd58d4466c00309765372dfdcf2d2b1f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5807e4af6cf40f283a2b331f80804838fd58d4466c00309765372dfdcf2d2b1f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/aes/cipher_fips197_kat_spec.spl
mirror: doc/06_spec/01_unit/lib/common/aes/cipher_fips197_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/aes/cipher_fips197_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/aes/cipher_fips197_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/aes/cipher_fips197_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/aes/cipher_fips197_kat_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces round key 0 equal to the cipher key itself' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/aes/cipher_fips197_kat_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the published w4..w7 (round key 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/aes/cipher_fips197_kat_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the published round key 1 as a contiguous 16-byte slice' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
