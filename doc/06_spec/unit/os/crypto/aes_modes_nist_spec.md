# Aes Modes Nist Specification

> Tests covering AES-OFB-128 NIST SP 800-38A Appendix F.4.1/F.4.2 vectors, AES-OFB-256 NIST SP 800-38A Appendix F.4.5/F.4.6 vectors, AES-CFB128-128 NIST SP 800-38A Appendix F.3.13/F.3.14 vectors, AES-CFB128-256 vectors (verified), AES-CFB8 NIST SP 800-38A Appendix F.3.7/F.3.8 vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Modes Nist Specification

## Scenarios

### AES-OFB-128 NIST SP 800-38A Appendix F.4.1/F.4.2 vectors

#### F.4.1 block 1 OFB-AES-128 encrypt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- F.4.1 block 1 OFB-AES-128 encrypt
   - Expected: _slice16(ct, 0) equals `_slice16(_ofb128_ct(), 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.1 block 1 OFB-AES-128 encrypt")
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_ofb128_ct(), 0))
```

</details>

#### F.4.1 block 2 OFB-AES-128 encrypt

- F.4.1 block 2 OFB-AES-128 encrypt
   - Expected: _slice16(ct, 1) equals `_slice16(_ofb128_ct(), 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.1 block 2 OFB-AES-128 encrypt")
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_ofb128_ct(), 1))
```

</details>

#### F.4.1 block 3 OFB-AES-128 encrypt

- F.4.1 block 3 OFB-AES-128 encrypt
   - Expected: _slice16(ct, 2) equals `_slice16(_ofb128_ct(), 2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.1 block 3 OFB-AES-128 encrypt")
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_ofb128_ct(), 2))
```

</details>

#### F.4.1 block 4 OFB-AES-128 encrypt

- F.4.1 block 4 OFB-AES-128 encrypt
   - Expected: _slice16(ct, 3) equals `_slice16(_ofb128_ct(), 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.1 block 4 OFB-AES-128 encrypt")
val ct = aes128_ofb_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_ofb128_ct(), 3))
```

</details>

#### F.4.2 OFB-AES-128 decrypt round-trip

- F.4.2 OFB-AES-128 decrypt round-trip
   - Expected: pt equals `_pt64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.2 OFB-AES-128 decrypt round-trip")
val pt = aes128_ofb_decrypt(_key128(), _iv(), _ofb128_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-OFB-256 NIST SP 800-38A Appendix F.4.5/F.4.6 vectors

#### F.4.5 block 1 OFB-AES-256 encrypt

- F.4.5 block 1 OFB-AES-256 encrypt
   - Expected: _slice16(ct, 0) equals `_slice16(_ofb256_ct(), 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.5 block 1 OFB-AES-256 encrypt")
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_ofb256_ct(), 0))
```

</details>

#### F.4.5 block 2 OFB-AES-256 encrypt

- F.4.5 block 2 OFB-AES-256 encrypt
   - Expected: _slice16(ct, 1) equals `_slice16(_ofb256_ct(), 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.5 block 2 OFB-AES-256 encrypt")
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_ofb256_ct(), 1))
```

</details>

#### F.4.5 block 3 OFB-AES-256 encrypt

- F.4.5 block 3 OFB-AES-256 encrypt
   - Expected: _slice16(ct, 2) equals `_slice16(_ofb256_ct(), 2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.5 block 3 OFB-AES-256 encrypt")
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_ofb256_ct(), 2))
```

</details>

#### F.4.5 block 4 OFB-AES-256 encrypt

- F.4.5 block 4 OFB-AES-256 encrypt
   - Expected: _slice16(ct, 3) equals `_slice16(_ofb256_ct(), 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.5 block 4 OFB-AES-256 encrypt")
val ct = aes256_ofb_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_ofb256_ct(), 3))
```

</details>

#### F.4.6 OFB-AES-256 decrypt round-trip

- F.4.6 OFB-AES-256 decrypt round-trip
   - Expected: pt equals `_pt64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.4.6 OFB-AES-256 decrypt round-trip")
val pt = aes256_ofb_decrypt(_key256(), _iv(), _ofb256_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-CFB128-128 NIST SP 800-38A Appendix F.3.13/F.3.14 vectors

#### F.3.13 block 1 AES-128-CFB128 encrypt

- F.3.13 block 1 AES-128-CFB128 encrypt
   - Expected: _slice16(ct, 0) equals `_slice16(_cfb128_128_ct(), 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.3.13 block 1 AES-128-CFB128 encrypt")
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_cfb128_128_ct(), 0))
```

</details>

#### F.3.13 block 2 AES-128-CFB128 encrypt

- F.3.13 block 2 AES-128-CFB128 encrypt
   - Expected: _slice16(ct, 1) equals `_slice16(_cfb128_128_ct(), 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.3.13 block 2 AES-128-CFB128 encrypt")
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_cfb128_128_ct(), 1))
```

</details>

#### F.3.13 block 3 AES-128-CFB128 encrypt

- F.3.13 block 3 AES-128-CFB128 encrypt
   - Expected: _slice16(ct, 2) equals `_slice16(_cfb128_128_ct(), 2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.3.13 block 3 AES-128-CFB128 encrypt")
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_cfb128_128_ct(), 2))
```

</details>

#### F.3.13 block 4 AES-128-CFB128 encrypt

- F.3.13 block 4 AES-128-CFB128 encrypt
   - Expected: _slice16(ct, 3) equals `_slice16(_cfb128_128_ct(), 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.3.13 block 4 AES-128-CFB128 encrypt")
val ct = aes128_cfb128_encrypt(_key128(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_cfb128_128_ct(), 3))
```

</details>

#### F.3.14 AES-128-CFB128 decrypt round-trip

- F.3.14 AES-128-CFB128 decrypt round-trip
   - Expected: pt equals `_pt64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.3.14 AES-128-CFB128 decrypt round-trip")
val pt = aes128_cfb128_decrypt(_key128(), _iv(), _cfb128_128_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-CFB128-256 vectors (verified)

#### AES-256-CFB128 block 1 encrypt

- AES-256-CFB128 block 1 encrypt
   - Expected: _slice16(ct, 0) equals `_slice16(_cfb128_256_ct(), 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AES-256-CFB128 block 1 encrypt")
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 0)).to_equal(_slice16(_cfb128_256_ct(), 0))
```

</details>

#### AES-256-CFB128 block 2 encrypt

- AES-256-CFB128 block 2 encrypt
   - Expected: _slice16(ct, 1) equals `_slice16(_cfb128_256_ct(), 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AES-256-CFB128 block 2 encrypt")
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 1)).to_equal(_slice16(_cfb128_256_ct(), 1))
```

</details>

#### AES-256-CFB128 block 3 encrypt

- AES-256-CFB128 block 3 encrypt
   - Expected: _slice16(ct, 2) equals `_slice16(_cfb128_256_ct(), 2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AES-256-CFB128 block 3 encrypt")
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 2)).to_equal(_slice16(_cfb128_256_ct(), 2))
```

</details>

#### AES-256-CFB128 block 4 encrypt

- AES-256-CFB128 block 4 encrypt
   - Expected: _slice16(ct, 3) equals `_slice16(_cfb128_256_ct(), 3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AES-256-CFB128 block 4 encrypt")
val ct = aes256_cfb128_encrypt(_key256(), _iv(), _pt64())
expect(_slice16(ct, 3)).to_equal(_slice16(_cfb128_256_ct(), 3))
```

</details>

#### AES-256-CFB128 decrypt round-trip

- AES-256-CFB128 decrypt round-trip
   - Expected: pt equals `_pt64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AES-256-CFB128 decrypt round-trip")
val pt = aes256_cfb128_decrypt(_key256(), _iv(), _cfb128_256_ct())
expect(pt).to_equal(_pt64())
```

</details>

### AES-CFB8 NIST SP 800-38A Appendix F.3.7/F.3.8 vectors

#### F.3.7 AES-128-CFB8 encrypts 18-byte plaintext correctly

- F.3.7 AES-128-CFB8 encrypts 18-byte plaintext correctly
   - Expected: ct equals `_cfb8_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.3.7 AES-128-CFB8 encrypts 18-byte plaintext correctly")
val ct = aes128_cfb8_encrypt(_key128(), _iv(), _cfb8_pt())
expect(ct).to_equal(_cfb8_ct())
```

</details>

#### F.3.8 AES-128-CFB8 decrypts back to plaintext

- F.3.8 AES-128-CFB8 decrypts back to plaintext
   - Expected: pt equals `_cfb8_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("F.3.8 AES-128-CFB8 decrypts back to plaintext")
val pt = aes128_cfb8_decrypt(_key128(), _iv(), _cfb8_ct())
expect(pt).to_equal(_cfb8_pt())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/aes_modes_nist_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-OFB-128 NIST SP 800-38A Appendix F.4.1/F.4.2 vectors, AES-OFB-256 NIST SP 800-38A Appendix F.4.5/F.4.6 vectors, AES-CFB128-128 NIST SP 800-38A Appendix F.3.13/F.3.14 vectors, AES-CFB128-256 vectors (verified), AES-CFB8 NIST SP 800-38A Appendix F.3.7/F.3.8 vectors.
- AES-OFB-128 NIST SP 800-38A Appendix F.4.1/F.4.2 vectors
- AES-OFB-256 NIST SP 800-38A Appendix F.4.5/F.4.6 vectors
- AES-CFB128-128 NIST SP 800-38A Appendix F.3.13/F.3.14 vectors
- AES-CFB128-256 vectors (verified)
- AES-CFB8 NIST SP 800-38A Appendix F.3.7/F.3.8 vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `bf2b97dce8b308be2e62cf4912e5aaf334e7358529bfb251c7869740c917b820`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf2b97dce8b308be2e62cf4912e5aaf334e7358529bfb251c7869740c917b820`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf2b97dce8b308be2e62cf4912e5aaf334e7358529bfb251c7869740c917b820`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/crypto/aes_modes_nist_spec.spl
mirror: doc/06_spec/unit/os/crypto/aes_modes_nist_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/aes_modes_nist_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/aes_modes_nist_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/aes_modes_nist_spec.spl:575:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F.4.1 block 1 OFB-AES-128 encrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/aes_modes_nist_spec.spl:581:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F.4.1 block 2 OFB-AES-128 encrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/aes_modes_nist_spec.spl:587:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'F.4.1 block 3 OFB-AES-128 encrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
