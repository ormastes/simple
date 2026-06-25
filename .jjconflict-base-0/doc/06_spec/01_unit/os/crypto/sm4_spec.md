# sm4_spec

> SM4 Block Cipher — Known-Answer Test Vectors

<!-- sdn-diagram:id=sm4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sm4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sm4_spec -> std
sm4_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sm4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/os/crypto/sm4_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
expect(_bytes_hex(ct)).to_equal("681edf34d206965e86b3e94f536e4246")
```

</details>

#### SM4 encrypt output is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
expect(ct.len()).to_equal(16)
```

</details>

#### SM4 decrypt vec1 CT recovers original plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = sm4_decrypt_block(_v1_key(), _v1_ct_expected())
expect(_bytes_hex(pt)).to_equal("0123456789abcdeffedcba9876543210")
```

</details>

#### SM4 encrypt/decrypt round-trip recovers plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
val pt = sm4_decrypt_block(_v1_key(), ct)
expect(_bytes_hex(pt)).to_equal("0123456789abcdeffedcba9876543210")
```

</details>

#### SM4 key_expand returns 32 round keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rk = sm4_key_expand(_v1_key())
expect(rk.len()).to_equal(32)
```

</details>

### SM4 — additional coverage

#### SM4 zero-key zero-pt round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = sm4_encrypt_block(_zero16(), _zero16())
val pt = sm4_decrypt_block(_zero16(), ct)
expect(_bytes_hex(pt)).to_equal("00000000000000000000000000000000")
```

</details>

#### SM4 encrypt ciphertext differs from plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = sm4_encrypt_block(_v1_key(), _v1_pt())
# Ciphertext must differ from plaintext (non-trivial encryption)
expect(_bytes_hex(ct)).to_equal("681edf34d206965e86b3e94f536e4246")
```

</details>

#### SM4 zero-key encrypt is deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
