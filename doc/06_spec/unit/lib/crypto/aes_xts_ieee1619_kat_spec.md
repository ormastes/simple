# Aes Xts Ieee1619 Kat Specification

> Tests covering AES-128-XTS IEEE 1619 TV1 (klen=32, len=32, sector=0, k1=k2=0), AES-128-XTS IEEE 1619 TV2 (klen=32, len=32, sector=0x3333333333), AES-128-XTS IEEE 1619 TV3 (klen=32, len=32, sector=0x3333333333), AES-128-XTS IEEE 1619 TV4 (klen=32, len=512, sector=0) — tweak doubling, AES-256-XTS IEEE 1619 TV10 (klen=64, len=512, sector=0xff), AES-128-XTS ciphertext-stealing partial-length (len=17, sector=0x123456789a).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Xts Ieee1619 Kat Specification

## Scenarios

### AES-128-XTS IEEE 1619 TV1 (klen=32, len=32, sector=0, k1=k2=0)

#### encrypts plaintext to TV1 ciphertext (917cf69e…)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encrypts plaintext to TV1 ciphertext (917cf69e…)
   - Expected: aes128_xts_encrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_pt()) equals `_tv1_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts plaintext to TV1 ciphertext (917cf69e…)")
expect(aes128_xts_encrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_pt())).to_equal(_tv1_ct())
```

</details>

#### decrypts TV1 ciphertext back to plaintext

- decrypts TV1 ciphertext back to plaintext
   - Expected: aes128_xts_decrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_ct()) equals `_tv1_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts TV1 ciphertext back to plaintext")
expect(aes128_xts_decrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_ct())).to_equal(_tv1_pt())
```

</details>

#### round-trips encrypt(decrypt(C)) == C

- round-trips encrypt(decrypt(C)) == C
   - Expected: aes128_xts_encrypt_sector(_tv1_key1(), _tv1_key2(), 0, pt) equals `_tv1_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips encrypt(decrypt(C)) == C")
val pt = aes128_xts_decrypt_sector(_tv1_key1(), _tv1_key2(), 0, _tv1_ct())
expect(aes128_xts_encrypt_sector(_tv1_key1(), _tv1_key2(), 0, pt)).to_equal(_tv1_ct())
```

</details>

### AES-128-XTS IEEE 1619 TV2 (klen=32, len=32, sector=0x3333333333)

#### encrypts plaintext to TV2 ciphertext (c454185e…)

- encrypts plaintext to TV2 ciphertext (c454185e…)
   - Expected: aes128_xts_encrypt_sector(_tv2_key1(), _tv2_key2(), 219902325555, _tv2_pt()) equals `_tv2_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts plaintext to TV2 ciphertext (c454185e…)")
expect(aes128_xts_encrypt_sector(_tv2_key1(), _tv2_key2(), 219902325555, _tv2_pt())).to_equal(_tv2_ct())
```

</details>

#### decrypts TV2 ciphertext back to plaintext

- decrypts TV2 ciphertext back to plaintext
   - Expected: aes128_xts_decrypt_sector(_tv2_key1(), _tv2_key2(), 219902325555, _tv2_ct()) equals `_tv2_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts TV2 ciphertext back to plaintext")
expect(aes128_xts_decrypt_sector(_tv2_key1(), _tv2_key2(), 219902325555, _tv2_ct())).to_equal(_tv2_pt())
```

</details>

### AES-128-XTS IEEE 1619 TV3 (klen=32, len=32, sector=0x3333333333)

#### encrypts plaintext to TV3 ciphertext (af85336b…)

- encrypts plaintext to TV3 ciphertext (af85336b…)
   - Expected: aes128_xts_encrypt_sector(_tv3_key1(), _tv3_key2(), 219902325555, _tv3_pt()) equals `_tv3_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts plaintext to TV3 ciphertext (af85336b…)")
expect(aes128_xts_encrypt_sector(_tv3_key1(), _tv3_key2(), 219902325555, _tv3_pt())).to_equal(_tv3_ct())
```

</details>

#### decrypts TV3 ciphertext back to plaintext

- decrypts TV3 ciphertext back to plaintext
   - Expected: aes128_xts_decrypt_sector(_tv3_key1(), _tv3_key2(), 219902325555, _tv3_ct()) equals `_tv3_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts TV3 ciphertext back to plaintext")
expect(aes128_xts_decrypt_sector(_tv3_key1(), _tv3_key2(), 219902325555, _tv3_ct())).to_equal(_tv3_pt())
```

</details>

### AES-128-XTS IEEE 1619 TV4 (klen=32, len=512, sector=0) — tweak doubling

#### encrypts 512-byte sector to TV4 ciphertext

- encrypts 512-byte sector to TV4 ciphertext
   - Expected: aes128_xts_encrypt_sector(_tv4_key1(), _tv4_key2(), 0, _tv4_pt()) equals `_tv4_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts 512-byte sector to TV4 ciphertext")
expect(aes128_xts_encrypt_sector(_tv4_key1(), _tv4_key2(), 0, _tv4_pt())).to_equal(_tv4_ct())
```

</details>

#### decrypts TV4 ciphertext back to plaintext

- decrypts TV4 ciphertext back to plaintext
   - Expected: aes128_xts_decrypt_sector(_tv4_key1(), _tv4_key2(), 0, _tv4_ct()) equals `_tv4_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts TV4 ciphertext back to plaintext")
expect(aes128_xts_decrypt_sector(_tv4_key1(), _tv4_key2(), 0, _tv4_ct())).to_equal(_tv4_pt())
```

</details>

### AES-256-XTS IEEE 1619 TV10 (klen=64, len=512, sector=0xff)

#### encrypts 512-byte sector to TV10 ciphertext (1c3b3a10…)

- encrypts 512-byte sector to TV10 ciphertext (1c3b3a10…)
   - Expected: aes256_xts_encrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_pt()) equals `_tv5_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts 512-byte sector to TV10 ciphertext (1c3b3a10…)")
expect(aes256_xts_encrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_pt())).to_equal(_tv5_ct())
```

</details>

#### decrypts TV10 ciphertext back to plaintext

- decrypts TV10 ciphertext back to plaintext
   - Expected: aes256_xts_decrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_ct()) equals `_tv5_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts TV10 ciphertext back to plaintext")
expect(aes256_xts_decrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_ct())).to_equal(_tv5_pt())
```

</details>

#### round-trips encrypt(decrypt(C)) == C

- round-trips encrypt(decrypt(C)) == C
   - Expected: aes256_xts_encrypt_sector(_tv5_key1(), _tv5_key2(), 255, pt) equals `_tv5_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips encrypt(decrypt(C)) == C")
val pt = aes256_xts_decrypt_sector(_tv5_key1(), _tv5_key2(), 255, _tv5_ct())
expect(aes256_xts_encrypt_sector(_tv5_key1(), _tv5_key2(), 255, pt)).to_equal(_tv5_ct())
```

</details>

### AES-128-XTS ciphertext-stealing partial-length (len=17, sector=0x123456789a)

#### encrypts 17-byte plaintext via CTS to ciphertext (6c1625db…)

- encrypts 17-byte plaintext via CTS to ciphertext (6c1625db…)
   - Expected: aes128_xts_encrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_pt()) equals `_cts17_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encrypts 17-byte plaintext via CTS to ciphertext (6c1625db…)")
# IEEE 1619 §5.4: one full block + 1-byte partial; CTS swaps last two
# output groups in computation but emits them in plaintext order.
expect(aes128_xts_encrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_pt())).to_equal(_cts17_ct())
```

</details>

#### decrypts 17-byte ciphertext via CTS back to plaintext

- decrypts 17-byte ciphertext via CTS back to plaintext
   - Expected: aes128_xts_decrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_ct()) equals `_cts17_pt()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decrypts 17-byte ciphertext via CTS back to plaintext")
expect(aes128_xts_decrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_ct())).to_equal(_cts17_pt())
```

</details>

#### round-trips CTS encrypt(decrypt(C)) == C

- round-trips CTS encrypt(decrypt(C)) == C
   - Expected: aes128_xts_encrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, pt) equals `_cts17_ct()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips CTS encrypt(decrypt(C)) == C")
val pt = aes128_xts_decrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, _cts17_ct())
expect(aes128_xts_encrypt_sector(_cts17_key1(), _cts17_key2(), 78187493530, pt)).to_equal(_cts17_ct())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AES-128-XTS IEEE 1619 TV1 (klen=32, len=32, sector=0, k1=k2=0), AES-128-XTS IEEE 1619 TV2 (klen=32, len=32, sector=0x3333333333), AES-128-XTS IEEE 1619 TV3 (klen=32, len=32, sector=0x3333333333), AES-128-XTS IEEE 1619 TV4 (klen=32, len=512, sector=0) — tweak doubling, AES-256-XTS IEEE 1619 TV10 (klen=64, len=512, sector=0xff), AES-128-XTS ciphertext-stealing partial-length (len=17, sector=0x123456789a).
- AES-128-XTS IEEE 1619 TV1 (klen=32, len=32, sector=0, k1=k2=0)
- AES-128-XTS IEEE 1619 TV2 (klen=32, len=32, sector=0x3333333333)
- AES-128-XTS IEEE 1619 TV3 (klen=32, len=32, sector=0x3333333333)
- AES-128-XTS IEEE 1619 TV4 (klen=32, len=512, sector=0) — tweak doubling
- AES-256-XTS IEEE 1619 TV10 (klen=64, len=512, sector=0xff)
- AES-128-XTS ciphertext-stealing partial-length (len=17, sector=0x123456789a)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `41516e764c9f22a25feadeda5d842b990e9ae8c31175acd02f39bd46182fe567`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `41516e764c9f22a25feadeda5d842b990e9ae8c31175acd02f39bd46182fe567`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `41516e764c9f22a25feadeda5d842b990e9ae8c31175acd02f39bd46182fe567`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl
mirror: doc/06_spec/unit/lib/crypto/aes_xts_ieee1619_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/aes_xts_ieee1619_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/aes_xts_ieee1619_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl:450:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encrypts plaintext to TV1 ciphertext (917cf69e…)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl:455:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decrypts TV1 ciphertext back to plaintext' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/aes_xts_ieee1619_kat_spec.spl:460:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips encrypt(decrypt(C)) == C' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
