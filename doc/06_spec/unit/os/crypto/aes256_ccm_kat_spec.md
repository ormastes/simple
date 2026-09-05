# Aes256 Ccm Kat Specification

> Tests covering aes256-ccm V1 -- empty AAD, 23-byte PT, tag_len=8 -- encrypt, aes256-ccm V1 -- decrypt round-trip and tamper detection, aes256-ccm V2 -- 8-byte AAD, 24-byte PT, tag_len=8 -- encrypt, aes256-ccm V3 -- 12-byte AAD, 24-byte PT, tag_len=12 -- encrypt.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes256 Ccm Kat Specification

## Scenarios

### aes256-ccm V1 -- empty AAD, 23-byte PT, tag_len=8 -- encrypt

#### V1 encrypt: ciphertext bytes match expected

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- V1 encrypt: ciphertext bytes match expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 encrypt: ciphertext bytes match expected")
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), _empty(), _v1_pt(), 8u32)
val ct = _slice_n(out, 0, 23)
expect(_bytes_hex(ct)).to_equal(
    "59615510a7c43bfb123d636b4613c03c6ce26907102a3f"
)
```

</details>

#### V1 encrypt: tag bytes match expected

- V1 encrypt: tag bytes match expected
   - Expected: _bytes_hex(tag) equals `a9340731cd6d4ded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 encrypt: tag bytes match expected")
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), _empty(), _v1_pt(), 8u32)
val tag = _slice_n(out, 23, 8)
expect(_bytes_hex(tag)).to_equal("a9340731cd6d4ded")
```

</details>

#### V1 encrypt: output length is PT_len + tag_len

- V1 encrypt: output length is PT_len + tag_len
   - Expected: out.len() equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 encrypt: output length is PT_len + tag_len")
val out = aes256_ccm_encrypt(_v1_key(), _v1_nonce(), _empty(), _v1_pt(), 8u32)
expect(out.len()).to_equal(31)
```

</details>

### aes256-ccm V1 -- decrypt round-trip and tamper detection

#### V1 decrypt: recovers original plaintext

- V1 decrypt: recovers original plaintext


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 decrypt: recovers original plaintext")
val pt = _unwrap_ok(aes256_ccm_decrypt(_v1_key(), _v1_nonce(), _empty(), _v1_ct(), _v1_tag()))
expect(_bytes_hex(pt)).to_equal(
    "08090a0b0c0d0e0f101112131415161718191a1b1c1d1e"
)
```

</details>

#### V1 decrypt with bad tag: returns Err

- V1 decrypt with bad tag: returns Err
   - Expected: _is_err(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V1 decrypt with bad tag: returns Err")
val r = aes256_ccm_decrypt(_v1_key(), _v1_nonce(), _empty(), _v1_ct(), _v1_tag_bad())
expect(_is_err(r)).to_equal(true)
```

</details>

### aes256-ccm V2 -- 8-byte AAD, 24-byte PT, tag_len=8 -- encrypt

#### V2 encrypt: ciphertext bytes match expected

- V2 encrypt: ciphertext bytes match expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V2 encrypt: ciphertext bytes match expected")
val out = aes256_ccm_encrypt(_v1_key(), _v2_nonce(), _v2_aad(), _v2_pt(), 8u32)
val ct = _slice_n(out, 0, 24)
expect(_bytes_hex(ct)).to_equal(
    "e2b4b743093bcc3a5e57d76a9a769efcae191b14773af31a"
)
```

</details>

#### V2 encrypt: tag bytes match expected

- V2 encrypt: tag bytes match expected
   - Expected: _bytes_hex(tag) equals `2273e08e81c40c6c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V2 encrypt: tag bytes match expected")
val out = aes256_ccm_encrypt(_v1_key(), _v2_nonce(), _v2_aad(), _v2_pt(), 8u32)
val tag = _slice_n(out, 24, 8)
expect(_bytes_hex(tag)).to_equal("2273e08e81c40c6c")
```

</details>

#### V2 decrypt: recovers original plaintext

- V2 decrypt: recovers original plaintext


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V2 decrypt: recovers original plaintext")
val pt = _unwrap_ok(aes256_ccm_decrypt(_v1_key(), _v2_nonce(), _v2_aad(), _v2_ct(), _v2_tag()))
expect(_bytes_hex(pt)).to_equal(
    "08090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
)
```

</details>

### aes256-ccm V3 -- 12-byte AAD, 24-byte PT, tag_len=12 -- encrypt

#### V3 encrypt: ciphertext bytes match expected

- V3 encrypt: ciphertext bytes match expected


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V3 encrypt: ciphertext bytes match expected")
val out = aes256_ccm_encrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_pt(), 12u32)
val ct = _slice_n(out, 0, 24)
expect(_bytes_hex(ct)).to_equal(
    "fc3ca91594f5e6bed5f6d005a89167a1718db3134f62ecee"
)
```

</details>

#### V3 encrypt: tag bytes match expected

- V3 encrypt: tag bytes match expected
   - Expected: _bytes_hex(tag) equals `d86e61a7a9103d31a2bf1e69`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V3 encrypt: tag bytes match expected")
val out = aes256_ccm_encrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_pt(), 12u32)
val tag = _slice_n(out, 24, 12)
expect(_bytes_hex(tag)).to_equal("d86e61a7a9103d31a2bf1e69")
```

</details>

#### V3 decrypt: recovers original plaintext

- V3 decrypt: recovers original plaintext


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V3 decrypt: recovers original plaintext")
val pt = _unwrap_ok(aes256_ccm_decrypt(_v3_key(), _v3_nonce(), _v3_aad(), _v3_ct(), _v3_tag()))
expect(_bytes_hex(pt)).to_equal(
    "202122232425262728292a2b2c2d2e2f3031323334353637"
)
```

</details>

#### V3 decrypt with tampered ciphertext: returns Err

- V3 decrypt with tampered ciphertext: returns Err
   - Expected: _is_err(r) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("V3 decrypt with tampered ciphertext: returns Err")
var bad_ct: [u8] = rt_array_new_with_cap(24)
bad_ct.push(0xFD)
var i: u64 = 1
while i < 24:
    bad_ct.push(_v3_ct()[i])
    i = i + 1
val r = aes256_ccm_decrypt(_v3_key(), _v3_nonce(), _v3_aad(), bad_ct, _v3_tag())
expect(_is_err(r)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/crypto/aes256_ccm_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aes256-ccm V1 -- empty AAD, 23-byte PT, tag_len=8 -- encrypt, aes256-ccm V1 -- decrypt round-trip and tamper detection, aes256-ccm V2 -- 8-byte AAD, 24-byte PT, tag_len=8 -- encrypt, aes256-ccm V3 -- 12-byte AAD, 24-byte PT, tag_len=12 -- encrypt.
- aes256-ccm V1 -- empty AAD, 23-byte PT, tag_len=8 -- encrypt
- aes256-ccm V1 -- decrypt round-trip and tamper detection
- aes256-ccm V2 -- 8-byte AAD, 24-byte PT, tag_len=8 -- encrypt
- aes256-ccm V3 -- 12-byte AAD, 24-byte PT, tag_len=12 -- encrypt

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `69c2b7fad8975d1ab461b67f58eede9e3150427d6d0a43a7bb3d9667b6944cbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `69c2b7fad8975d1ab461b67f58eede9e3150427d6d0a43a7bb3d9667b6944cbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `69c2b7fad8975d1ab461b67f58eede9e3150427d6d0a43a7bb3d9667b6944cbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/crypto/aes256_ccm_kat_spec.spl
mirror: doc/06_spec/unit/os/crypto/aes256_ccm_kat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/crypto/aes256_ccm_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/crypto/aes256_ccm_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/crypto/aes256_ccm_kat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/crypto/aes256_ccm_kat_spec.spl:496:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V1 encrypt: ciphertext bytes match expected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/aes256_ccm_kat_spec.spl:505:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V1 encrypt: tag bytes match expected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/crypto/aes256_ccm_kat_spec.spl:512:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V1 encrypt: output length is PT_len + tag_len' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
