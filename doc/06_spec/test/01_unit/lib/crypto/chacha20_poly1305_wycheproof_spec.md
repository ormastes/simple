# Chacha20 Poly1305 Wycheproof Specification

> <details>

<!-- sdn-diagram:id=chacha20_poly1305_wycheproof_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chacha20_poly1305_wycheproof_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chacha20_poly1305_wycheproof_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chacha20_poly1305_wycheproof_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chacha20 Poly1305 Wycheproof Specification

## Scenarios

### ChaCha20-Poly1305 boundary — empty PT + empty AAD

#### seal produces empty ciphertext, 16-byte tag (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Boundary vector: key=00..1f, nonce=00..0b, empty PT, empty AAD
# tag: 295a498b8841a1c5f55d4d606f731159
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, empty)
expect(ct.len()).to_equal(0u64)
expect(_bytes_eq_b(tag, _tag_size0())).to_equal(true)
```

</details>

#### round-trip: open(seal(empty)) recovers empty plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, empty)
expect(_open_len_b(_key_b(), _nonce_b(), empty, ct, tag)).to_equal(0u64)
```

</details>

### ChaCha20-Poly1305 boundary — empty PT + 16-byte AAD

#### seal with 16-byte AAD + empty PT produces correct tag (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Boundary vector: key=00..1f, nonce=00..0b, empty PT, aad=10..1f
# tag: 7747d1fc06fb33eebb1acab76747ff42
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), _aad_16b(), empty)
expect(ct.len()).to_equal(0u64)
expect(_bytes_eq_b(tag, _tag_emptyPT_aad16())).to_equal(true)
```

</details>

#### round-trip: open(seal(empty, aad16)) recovers empty plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), _aad_16b(), empty)
expect(_open_eq_b(_key_b(), _nonce_b(), _aad_16b(), ct, tag, empty)).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 1-byte PT

#### seal 1-byte PT produces 1-byte ciphertext + correct tag (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PT=00, empty AAD → ct=89, tag=04f0dd71889fd631f90e4584d25cbb92
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(1u64))
expect(ct.len()).to_equal(1u64)
expect(_bytes_eq_b(ct, _ct_size1())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size1())).to_equal(true)
```

</details>

#### round-trip: 1-byte PT recovered correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(1u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(1u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 16-byte PT (one Poly1305 block)

#### seal 16-byte PT: ciphertext byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Exact Poly1305 block boundary — padding path exercises 0 pad bytes
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(16u64))
expect(_bytes_eq_b(ct, _ct_size16())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size16())).to_equal(true)
```

</details>

#### round-trip: 16-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(16u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(16u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 17-byte PT (one block + 1 residual)

#### seal 17-byte PT: ciphertext byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First residual byte exercises the Poly1305 partial-block path
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(17u64))
expect(_bytes_eq_b(ct, _ct_size17())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size17())).to_equal(true)
```

</details>

#### round-trip: 17-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(17u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(17u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 31-byte PT (just under two Poly1305 blocks)

#### seal 31-byte PT: ciphertext byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(31u64))
expect(_bytes_eq_b(ct, _ct_size31())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size31())).to_equal(true)
```

</details>

#### round-trip: 31-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(31u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(31u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 32-byte PT (exact two Poly1305 blocks)

#### seal 32-byte PT: ciphertext byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(32u64))
expect(_bytes_eq_b(ct, _ct_size32())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size32())).to_equal(true)
```

</details>

#### round-trip: 32-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(32u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(32u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 64-byte PT (one full ChaCha20 block)

#### seal 64-byte PT: ciphertext byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 64 bytes = exactly one ChaCha20 block; counter stays at 1
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(64u64))
expect(_bytes_eq_b(ct, _ct_size64())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size64())).to_equal(true)
```

</details>

#### round-trip: 64-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(64u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(64u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 65-byte PT (forces ChaCha20 counter increment)

#### seal 65-byte PT: ciphertext byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 65 bytes = 64 + 1; the 65th byte requires ChaCha20 counter=2
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(65u64))
expect(_bytes_eq_b(ct, _ct_size65())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size65())).to_equal(true)
```

</details>

#### round-trip: 65-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(65u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(65u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 128-byte PT (two full ChaCha20 blocks)

#### seal 128-byte PT: ciphertext byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(128u64))
expect(_bytes_eq_b(ct, _ct_size128())).to_equal(true)
expect(_bytes_eq_b(tag, _tag_size128())).to_equal(true)
```

</details>

#### round-trip: 128-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_n(128u64))
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_n(128u64))).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — 1024-byte PT (16 full ChaCha20 blocks)

#### seal 1024-byte PT: tag byte-exact (KAT)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1024 bytes = 16 ChaCha20 blocks; exercises counter from 1 to 16
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_1024())
expect(ct.len()).to_equal(1024u64)
expect(_bytes_eq_b(tag, _tag_size1024())).to_equal(true)
```

</details>

#### round-trip: 1024-byte PT recovered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(_key_b(), _nonce_b(), empty, _pt_1024())
expect(_open_eq_b(_key_b(), _nonce_b(), empty, ct, tag, _pt_1024())).to_equal(true)
```

</details>

### ChaCha20-Poly1305 boundary — tag-length rejection

#### open with 0-byte tag returns nil (tag.len() != 16 early-reject)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# M2's open explicitly checks tag.len() != 16 → returns nil immediately
val empty: [u8] = []
val zero_tag: [u8] = []
expect(_open_is_nil_b(_key_b(), _nonce_b(), empty, _ct_size1(), zero_tag)).to_equal(true)
```

</details>

#### open with 15-byte tag returns nil (tag.len() != 16 early-reject)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val short_tag: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8,
                       0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8, 0x0du8, 0x0eu8]
expect(_open_is_nil_b(_key_b(), _nonce_b(), empty, _ct_size1(), short_tag)).to_equal(true)
```

</details>

#### open with 17-byte tag returns nil (tag.len() != 16 early-reject)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val long_tag: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8,
                      0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8, 0x0du8, 0x0eu8, 0x0fu8,
                      0x10u8]
expect(_open_is_nil_b(_key_b(), _nonce_b(), empty, _ct_size1(), long_tag)).to_equal(true)
```

</details>

### ChaCha20-Poly1305 Wycheproof — valid vectors

#### tcId 2 (Pseudorandom): empty msg, empty AAD → correct tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 2, flags=[Pseudorandom], result=valid
# key: 80ba3192c803ce965ea371d5ff073cf0f43b6a2ab576b208426e11409c09b9b0
# iv:  4da5bf8dfd5852c1ea12379d
# tag: 76acb342cf3166a5b63c0c0ea1383c8d
val key: [u8] = [0x80u8, 0xbau8, 0x31u8, 0x92u8, 0xc8u8, 0x03u8, 0xceu8, 0x96u8,
                 0x5eu8, 0xa3u8, 0x71u8, 0xd5u8, 0xffu8, 0x07u8, 0x3cu8, 0xf0u8,
                 0xf4u8, 0x3bu8, 0x6au8, 0x2au8, 0xb5u8, 0x76u8, 0xb2u8, 0x08u8,
                 0x42u8, 0x6eu8, 0x11u8, 0x40u8, 0x9cu8, 0x09u8, 0xb9u8, 0xb0u8]
val nonce: [u8] = [0x4du8, 0xa5u8, 0xbfu8, 0x8du8, 0xfdu8, 0x58u8, 0x52u8, 0xc1u8,
                   0xeau8, 0x12u8, 0x37u8, 0x9du8]
val expected_tag: [u8] = [0x76u8, 0xacu8, 0xb3u8, 0x42u8, 0xcfu8, 0x31u8, 0x66u8, 0xa5u8,
                          0xb6u8, 0x3cu8, 0x0cu8, 0x0eu8, 0xa1u8, 0x38u8, 0x3cu8, 0x8du8]
val empty: [u8] = []
val (_ct, tag) = chacha20_poly1305_seal(key, nonce, empty, empty)
expect(_bytes_eq_b(tag, expected_tag)).to_equal(true)
```

</details>

#### tcId 3 (Pseudorandom): empty msg, 8-byte AAD → correct tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 3, flags=[Pseudorandom], result=valid
# key: 7a4cd759172e02eb204db2c3f5c746227df584fc1345196391dbb9577a250742
# iv:  a92ef0ac991dd516a3c6f689
# aad: bd506764f2d2c410
# tag: 906fa6284b52f87b7359cbaa7563c709
val key: [u8] = [0x7au8, 0x4cu8, 0xd7u8, 0x59u8, 0x17u8, 0x2eu8, 0x02u8, 0xebu8,
                 0x20u8, 0x4du8, 0xb2u8, 0xc3u8, 0xf5u8, 0xc7u8, 0x46u8, 0x22u8,
                 0x7du8, 0xf5u8, 0x84u8, 0xfcu8, 0x13u8, 0x45u8, 0x19u8, 0x63u8,
                 0x91u8, 0xdbu8, 0xb9u8, 0x57u8, 0x7au8, 0x25u8, 0x07u8, 0x42u8]
val nonce: [u8] = [0xa9u8, 0x2eu8, 0xf0u8, 0xacu8, 0x99u8, 0x1du8, 0xd5u8, 0x16u8,
                   0xa3u8, 0xc6u8, 0xf6u8, 0x89u8]
val aad: [u8] = [0xbdu8, 0x50u8, 0x67u8, 0x64u8, 0xf2u8, 0xd2u8, 0xc4u8, 0x10u8]
val expected_tag: [u8] = [0x90u8, 0x6fu8, 0xa6u8, 0x28u8, 0x4bu8, 0x52u8, 0xf8u8, 0x7bu8,
                          0x73u8, 0x59u8, 0xcbu8, 0xaau8, 0x75u8, 0x63u8, 0xc7u8, 0x09u8]
val empty: [u8] = []
val (_ct, tag) = chacha20_poly1305_seal(key, nonce, aad, empty)
expect(_bytes_eq_b(tag, expected_tag)).to_equal(true)
```

</details>

#### tcId 4 (Pseudorandom): 1-byte msg, empty AAD → ct+tag byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 4, flags=[Pseudorandom], result=valid
# key: cc56b680552eb75008f5484b4cb803fa5063ebd6eab91f6ab6aef4916a766273
# iv:  99e23ec48985bccdeeab60f1
# msg: 2a → ct: 3a, tag: cac27dec0968801e9f6eded69d807522
val key: [u8] = [0xccu8, 0x56u8, 0xb6u8, 0x80u8, 0x55u8, 0x2eu8, 0xb7u8, 0x50u8,
                 0x08u8, 0xf5u8, 0x48u8, 0x4bu8, 0x4cu8, 0xb8u8, 0x03u8, 0xfau8,
                 0x50u8, 0x63u8, 0xebu8, 0xd6u8, 0xeau8, 0xb9u8, 0x1fu8, 0x6au8,
                 0xb6u8, 0xaeu8, 0xf4u8, 0x91u8, 0x6au8, 0x76u8, 0x62u8, 0x73u8]
val nonce: [u8] = [0x99u8, 0xe2u8, 0x3eu8, 0xc4u8, 0x89u8, 0x85u8, 0xbcu8, 0xcdu8,
                   0xeeu8, 0xabu8, 0x60u8, 0xf1u8]
val msg: [u8] = [0x2au8]
val expected_ct: [u8] = [0x3au8]
val expected_tag: [u8] = [0xcau8, 0xc2u8, 0x7du8, 0xecu8, 0x09u8, 0x68u8, 0x80u8, 0x1eu8,
                          0x9fu8, 0x6eu8, 0xdeu8, 0xd6u8, 0x9du8, 0x80u8, 0x75u8, 0x22u8]
val empty: [u8] = []
val (ct, tag) = chacha20_poly1305_seal(key, nonce, empty, msg)
expect(_bytes_eq_b(ct, expected_ct)).to_equal(true)
expect(_bytes_eq_b(tag, expected_tag)).to_equal(true)
```

</details>

#### tcId 5 (Pseudorandom): 1-byte msg, 8-byte AAD → ct+tag byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 5, flags=[Pseudorandom], result=valid
# key: 46f0254965f769d52bdb4a70b443199f8ef207520d1220c55e4b70f0fda620ee
# iv:  ab0dca716ee051d2782f4403
# aad: 91ca6c592cbcca53, msg: 51 → ct: c4, tag: 168310ca45b1f7c66cad4e99e43f72b9
val key: [u8] = [0x46u8, 0xf0u8, 0x25u8, 0x49u8, 0x65u8, 0xf7u8, 0x69u8, 0xd5u8,
                 0x2bu8, 0xdbu8, 0x4au8, 0x70u8, 0xb4u8, 0x43u8, 0x19u8, 0x9fu8,
                 0x8eu8, 0xf2u8, 0x07u8, 0x52u8, 0x0du8, 0x12u8, 0x20u8, 0xc5u8,
                 0x5eu8, 0x4bu8, 0x70u8, 0xf0u8, 0xfdu8, 0xa6u8, 0x20u8, 0xeeu8]
val nonce: [u8] = [0xabu8, 0x0du8, 0xcau8, 0x71u8, 0x6eu8, 0xe0u8, 0x51u8, 0xd2u8,
                   0x78u8, 0x2fu8, 0x44u8, 0x03u8]
val aad: [u8] = [0x91u8, 0xcau8, 0x6cu8, 0x59u8, 0x2cu8, 0xbcu8, 0xcau8, 0x53u8]
val msg: [u8] = [0x51u8]
val expected_ct: [u8] = [0xc4u8]
val expected_tag: [u8] = [0x16u8, 0x83u8, 0x10u8, 0xcau8, 0x45u8, 0xb1u8, 0xf7u8, 0xc6u8,
                          0x6cu8, 0xadu8, 0x4eu8, 0x99u8, 0xe4u8, 0x3fu8, 0x72u8, 0xb9u8]
val (ct, tag) = chacha20_poly1305_seal(key, nonce, aad, msg)
expect(_bytes_eq_b(ct, expected_ct)).to_equal(true)
expect(_bytes_eq_b(tag, expected_tag)).to_equal(true)
```

</details>

### ChaCha20-Poly1305 Wycheproof — ModifiedTag (AUTH_BYPASS)

#### tcId 148 (ModifiedTag, bit-7 flip): open returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 148, flags=[ModifiedTag], result=invalid
# expected tag: f4409bb729039d0814ac514054323f44
# modified tag: 74409bb729039d0814ac514054323f44  (bit 7 of byte 0 flipped)
val empty: [u8] = []
val bad_tag: [u8] = [0x74u8, 0x40u8, 0x9bu8, 0xb7u8, 0x29u8, 0x03u8, 0x9du8, 0x08u8,
                     0x14u8, 0xacu8, 0x51u8, 0x40u8, 0x54u8, 0x32u8, 0x3fu8, 0x44u8]
expect(_open_is_nil_b(_wyc_key_2021(), _wyc_nonce_0001(), _wyc_aad_000102(), empty, bad_tag)).to_equal(true)
```

</details>

#### tcId 149 (ModifiedTag, bit-8 flip): open returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 149, flags=[ModifiedTag], result=invalid
# modified tag: f4419bb729039d0814ac514054323f44  (bit 8 = byte 1 bit 0)
val empty: [u8] = []
val bad_tag: [u8] = [0xf4u8, 0x41u8, 0x9bu8, 0xb7u8, 0x29u8, 0x03u8, 0x9du8, 0x08u8,
                     0x14u8, 0xacu8, 0x51u8, 0x40u8, 0x54u8, 0x32u8, 0x3fu8, 0x44u8]
expect(_open_is_nil_b(_wyc_key_2021(), _wyc_nonce_0001(), _wyc_aad_000102(), empty, bad_tag)).to_equal(true)
```

</details>

#### tcId 164 (ModifiedTag, all-zero tag): open returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 164, flags=[ModifiedTag], result=invalid
# all-zero tag must never authenticate
val empty: [u8] = []
val zero_tag: [u8] = [0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8,
                      0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8, 0x00u8]
expect(_open_is_nil_b(_wyc_key_2021(), _wyc_nonce_0001(), _wyc_aad_000102(), empty, zero_tag)).to_equal(true)
```

</details>

#### valid seal tag for Wycheproof key/nonce/aad is byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Positive control: the valid tag that the ModifiedTag tests are mutating
val empty: [u8] = []
val (_ct, tag) = chacha20_poly1305_seal(_wyc_key_2021(), _wyc_nonce_0001(), _wyc_aad_000102(), empty)
expect(_bytes_eq_b(tag, _wyc_valid_tag_empty_msg())).to_equal(true)
```

</details>

### ChaCha20-Poly1305 Wycheproof — InvalidNonceSize

#### tcId 320 (InvalidNonceSize, 13-byte nonce): open returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 320, flags=[InvalidNonceSize], result=invalid
# API note: Simple's open does not explicitly enforce nonce length.
# A wrong-length nonce produces a wrong keystream → tag mismatch → nil.
val nonce_13: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8,
                      0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8]
val empty: [u8] = []
# Use any 16-byte tag; with the wrong nonce the MAC will not verify.
expect(_open_is_nil_b(_wyc_key_2021(), nonce_13, empty, empty, _wyc_valid_tag_empty_msg())).to_equal(true)
```

</details>

#### tcId 322 (InvalidNonceSize, 16-byte nonce): open returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Wycheproof tcId 322, flags=[InvalidNonceSize], result=invalid
val nonce_16: [u8] = [0x00u8, 0x01u8, 0x02u8, 0x03u8, 0x04u8, 0x05u8, 0x06u8, 0x07u8,
                      0x08u8, 0x09u8, 0x0au8, 0x0bu8, 0x0cu8, 0x0du8, 0x0eu8, 0x0fu8]
val empty: [u8] = []
expect(_open_is_nil_b(_wyc_key_2021(), nonce_16, empty, empty, _wyc_valid_tag_empty_msg())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/chacha20_poly1305_wycheproof_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ChaCha20-Poly1305 boundary — empty PT + empty AAD
- ChaCha20-Poly1305 boundary — empty PT + 16-byte AAD
- ChaCha20-Poly1305 boundary — 1-byte PT
- ChaCha20-Poly1305 boundary — 16-byte PT (one Poly1305 block)
- ChaCha20-Poly1305 boundary — 17-byte PT (one block + 1 residual)
- ChaCha20-Poly1305 boundary — 31-byte PT (just under two Poly1305 blocks)
- ChaCha20-Poly1305 boundary — 32-byte PT (exact two Poly1305 blocks)
- ChaCha20-Poly1305 boundary — 64-byte PT (one full ChaCha20 block)
- ChaCha20-Poly1305 boundary — 65-byte PT (forces ChaCha20 counter increment)
- ChaCha20-Poly1305 boundary — 128-byte PT (two full ChaCha20 blocks)
- ChaCha20-Poly1305 boundary — 1024-byte PT (16 full ChaCha20 blocks)
- ChaCha20-Poly1305 boundary — tag-length rejection
- ChaCha20-Poly1305 Wycheproof — valid vectors
- ChaCha20-Poly1305 Wycheproof — ModifiedTag (AUTH_BYPASS)
- ChaCha20-Poly1305 Wycheproof — InvalidNonceSize

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
