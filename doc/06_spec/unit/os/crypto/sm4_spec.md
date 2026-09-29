# sm4_spec

> SM4 Block Cipher — Known-Answer Test Vectors

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sm4_spec

SM4 Block Cipher — Known-Answer Test Vectors

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/sm4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SM4 Block Cipher — Known-Answer Test Vectors

Tests sm4_encrypt_block, sm4_decrypt_block, and sm4_key_expand against
the official GM/T 0002-2012 / GB/T 32907-2016 test vector.

Vector 1 (from the standard):
  Key:        0123456789ABCDEFFEDCBA9876543210
  Plaintext:  0123456789ABCDEFFEDCBA9876543210
  Ciphertext: 681EDF34D206965E86B3E94F536E4246

Source: GM/T 0002-2012 §A.1 (official SM4 standard)
https://www.gmbz.org.cn/upload/2018-07-24/1532401392842079739.pdf

NOTE: Verified in interpreter mode per feedback_compile_mode_false_greens.md.
The 1-million-iteration endurance test is skipped in interpreter mode due to
interpreter performance (documented limitation, not a bug).

## Scenarios

### SM4 — GB/T 32907-2016 known-answer vector

#### SM4 encrypt vec1 -> 681edf34d206965e86b3e94f536e4246

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SM4 encrypt vec1 -> 681edf34d206965e86b3e94f536e4246
   - Expected: _bytes_hex(ct) equals `681edf34d206965e86b3e94f536e4246`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 encrypt vec1 -> 681edf34d206965e86b3e94f536e4246")
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
expect(_bytes_hex(ct)).to_equal("681edf34d206965e86b3e94f536e4246")
```

</details>

#### SM4 encrypt output is 16 bytes

- SM4 encrypt output is 16 bytes
   - Expected: ct.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 encrypt output is 16 bytes")
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### SM4 decrypt vec1 CT recovers original plaintext

- SM4 decrypt vec1 CT recovers original plaintext
   - Expected: _bytes_hex(pt) equals `0123456789abcdeffedcba9876543210`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 decrypt vec1 CT recovers original plaintext")
val pt = sm4_decrypt_block(_v1_key(), _v1_ct_expected())
expect(_bytes_hex(pt)).to_equal("0123456789abcdeffedcba9876543210")
```

</details>

#### SM4 encrypt/decrypt round-trip recovers plaintext

- SM4 encrypt/decrypt round-trip recovers plaintext
   - Expected: _bytes_hex(pt) equals `0123456789abcdeffedcba9876543210`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 encrypt/decrypt round-trip recovers plaintext")
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
val pt = sm4_decrypt_block(_v1_key(), ct)
expect(_bytes_hex(pt)).to_equal("0123456789abcdeffedcba9876543210")
```

</details>

#### SM4 key_expand returns 32 round keys

- SM4 key_expand returns 32 round keys
   - Expected: rk.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 key_expand returns 32 round keys")
val rk = sm4_key_expand(_v1_key())
expect(rk.len()).to_equal(32)
```

</details>

### SM4 — additional coverage

#### SM4 zero-key zero-pt round-trip

- SM4 zero-key zero-pt round-trip
   - Expected: _bytes_hex(pt) equals `00000000000000000000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 zero-key zero-pt round-trip")
val ct = sm4_encrypt_block(_zero16(), _zero16())
val pt = sm4_decrypt_block(_zero16(), ct)
expect(_bytes_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### SM4 encrypt ciphertext differs from plaintext

- SM4 encrypt ciphertext differs from plaintext
   - Expected: _bytes_hex(ct) equals `681edf34d206965e86b3e94f536e4246`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 encrypt ciphertext differs from plaintext")
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
# Ciphertext must differ from plaintext (non-trivial encryption)
expect(_bytes_hex(ct)).to_equal("681edf34d206965e86b3e94f536e4246")
```

</details>

#### SM4 zero-key encrypt is deterministic

- SM4 zero-key encrypt is deterministic
   - Expected: _bytes_hex(ct1) equals `_bytes_hex(ct2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SM4 zero-key encrypt is deterministic")
val ct1 = sm4_encrypt_block(_zero16(), _zero16())
val ct2 = sm4_encrypt_block(_zero16(), _zero16())
expect(_bytes_hex(ct1)).to_equal(_bytes_hex(ct2))
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe40245baac0d2ccbec539b3bd9a32156897c9adf4b4ccd76471a47377283ac1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe40245baac0d2ccbec539b3bd9a32156897c9adf4b4ccd76471a47377283ac1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe40245baac0d2ccbec539b3bd9a32156897c9adf4b4ccd76471a47377283ac1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/crypto/sm4_spec.spl
mirror: doc/06_spec/unit/os/crypto/sm4_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/sm4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/sm4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/sm4_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/sm4_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SM4 encrypt vec1 -> 681edf34d206965e86b3e94f536e4246' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sm4_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SM4 encrypt output is 16 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/sm4_spec.spl:181:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SM4 decrypt vec1 CT recovers original plaintext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
