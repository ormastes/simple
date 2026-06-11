# Intrinsic Lowering Aarch64 Specification

> 1. var result = intrinsic to target idiom aarch64

<!-- sdn-diagram:id=intrinsic_lowering_aarch64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=intrinsic_lowering_aarch64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

intrinsic_lowering_aarch64_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=intrinsic_lowering_aarch64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intrinsic Lowering Aarch64 Specification

## Scenarios

### intrinsic_to_target_idiom_aarch64 — name mapping

#### crypto_aes_round maps to AesEnc idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("crypto_aes_round")
expect(result.is_some()).to_equal(true)
```

</details>

#### crypto_aes_round_last maps to AesEncLast idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("crypto_aes_round_last")
expect(result.is_some()).to_equal(true)
```

</details>

#### clmul_lo maps to ClmulLo idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("clmul_lo")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_popcount maps to Popcount idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("bit_popcount")
expect(result.is_some()).to_equal(true)
```

</details>

<details>
<summary>Advanced: matrix_dot maps to MatrixDot idiom</summary>

#### matrix_dot maps to MatrixDot idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("matrix_dot")
expect(result.is_some()).to_equal(true)
```

</details>


</details>

#### crypto_sha512_rnds2 maps to Sha512Rounds2 idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("crypto_sha512_rnds2")
expect(result.is_some()).to_equal(true)
```

</details>

#### crypto_sha512_msg1 maps to Sha512Msg1 idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("crypto_sha512_msg1")
expect(result.is_some()).to_equal(true)
```

</details>

#### crypto_sha512_msg2 maps to Sha512Msg2 idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("crypto_sha512_msg2")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_rotate_left maps to RotateLeft idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("bit_rotate_left")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_rotate_right maps to RotateRight idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("bit_rotate_right")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_parity maps to Parity idiom

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("bit_parity")
expect(result.is_some()).to_equal(true)
```

</details>

#### unknown name returns nil

1. var result = intrinsic to target idiom aarch64
   - Expected: result.is_some() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = intrinsic_to_target_idiom_aarch64("not_a_real_intrinsic")
expect(result.is_some()).to_equal(false)
```

</details>

### lower_cipher_intrinsic_aarch64 — AES lowering with crypto caps

#### crypto_aes_round emits 8 bytes (AESE+AESMC pair)

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crypto_aes_round_last emits 4 bytes (AESE only)

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round_last", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crypto_aes_inv_round emits 8 bytes (AESD+AESIMC pair)

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crypto_aes_inv_round_last emits 4 bytes (AESD only)

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round_last", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

### lower_cipher_intrinsic_aarch64 — bare Aarch64Caps refuses cipher idioms

#### AES round on bare caps returns lowered=false, reason='no-cap'

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### SHA256 rnds2 on bare caps refuses

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [0, 1, 2], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### CRC32_U8 on bare caps refuses

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crc32_u8", [0, 1, 2], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### CLMUL_LO on bare caps refuses

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("clmul_lo", [0, 1, 2], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

### lower_cipher_intrinsic_aarch64 — unknown name handling

#### unrecognised intrinsic returns lowered=false, reason='unknown'

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("not_a_real_intrinsic", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

#### empty name returns unknown

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("", [], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

### lower_cipher_intrinsic_aarch64 — SHA256 / CRC32 / CLMUL on full caps

#### crypto_sha256_rnds2 emits 8 bytes (SHA256H+SHA256H2) when has_sha2

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crc32_u8 lowers when has_crc32

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crc32_u8", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crc32_u32 lowers when has_crc32

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crc32_u32", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crc32_u64 lowers when has_crc32

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crc32_u64", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### clmul_lo emits PMULL when has_pmull

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("clmul_lo", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### clmul_hi emits PMULL2 when has_pmull

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("clmul_hi", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

### lower_cipher_intrinsic_aarch64 — arity checking

#### crypto_aes_round with 3 args returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0, 1, 2], caps_aes_only())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### clmul_lo with 2 args returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("clmul_lo", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

### lower_cipher_intrinsic_aarch64 — portable bit/matrix scaffolding

#### bit_bswap lowers on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_bswap", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_clz lowers on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_clz", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_ctz lowers on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_ctz", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### bit_bitreverse lowers on sve2-capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_bitreverse", [0, 1], caps_sve2())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_popcount stays on the current non-direct path on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_popcount", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

#### bit_clz with 1 arg returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_clz", [0], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_ctz with 1 arg returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_ctz", [0], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_bitreverse with 1 arg returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_bitreverse", [0], caps_sve2())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

<details>
<summary>Advanced: matrix_dot is recognised and returns unimplemented on capable caps</summary>

#### matrix_dot is recognised and returns unimplemented on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("matrix_dot", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unimplemented")
```

</details>


</details>

### lower_cipher_intrinsic_aarch64 — SHA-512 lowering

#### crypto_sha512_rnds2 emits 8 bytes (SHA512H+SHA512H2) when has_sha512

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_rnds2", [0, 1, 2], caps_sha512())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crypto_sha512_msg1 emits 4 bytes (SHA512SU0) when has_sha512

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg1", [0, 1], caps_sha512())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crypto_sha512_msg2 emits 4 bytes (SHA512SU1) when has_sha512

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg2", [0, 1, 2], caps_sha512())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crypto_sha512_rnds2 on caps without has_sha512 returns no-cap

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_rnds2", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### crypto_sha512_msg1 on caps without has_sha512 returns no-cap

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg1", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### crypto_sha512_rnds2 with 2 args returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_rnds2", [0, 1], caps_sha512())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### crypto_sha512_msg1 with 3 args returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg1", [0, 1, 2], caps_sha512())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### crypto_sha512_msg2 with 2 args returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg2", [0, 1], caps_sha512())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

### lower_cipher_intrinsic_aarch64 — rotate lowering

#### bit_rotate_right emits 4 bytes (EXTR/ROR) on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_rotate_right", [0, 1, 7], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_rotate_left emits 4 bytes (EXTR/ROR neg) on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_rotate_left", [0, 1, 7], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_rotate_right with 2 args returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_rotate_right", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_rotate_left with 2 args returns bad-arity

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_rotate_left", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

### lower_cipher_intrinsic_aarch64 — parity lowering

#### bit_parity returns unimplemented on capable caps

1. var r = lower cipher intrinsic aarch64
   - Expected: r.lowered is false
   - Expected: r.reason equals `unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = lower_cipher_intrinsic_aarch64("bit_parity", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unimplemented")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- intrinsic_to_target_idiom_aarch64 — name mapping
- lower_cipher_intrinsic_aarch64 — AES lowering with crypto caps
- lower_cipher_intrinsic_aarch64 — bare Aarch64Caps refuses cipher idioms
- lower_cipher_intrinsic_aarch64 — unknown name handling
- lower_cipher_intrinsic_aarch64 — SHA256 / CRC32 / CLMUL on full caps
- lower_cipher_intrinsic_aarch64 — arity checking
- lower_cipher_intrinsic_aarch64 — portable bit/matrix scaffolding
- lower_cipher_intrinsic_aarch64 — SHA-512 lowering
- lower_cipher_intrinsic_aarch64 — rotate lowering
- lower_cipher_intrinsic_aarch64 — parity lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
