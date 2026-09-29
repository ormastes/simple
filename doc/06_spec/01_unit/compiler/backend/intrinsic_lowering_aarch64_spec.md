# intrinsic_lowering_aarch64_spec

> Purpose: Prove that intrinsic_to_target_idiom_aarch64 — name mapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# intrinsic_lowering_aarch64_spec

Purpose: Prove that intrinsic_to_target_idiom_aarch64 — name mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that intrinsic_to_target_idiom_aarch64 — name mapping.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### intrinsic_to_target_idiom_aarch64 — name mapping

#### crypto_aes_round maps to AesEnc idiom

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- crypto_aes_round maps to AesEnc idiom
- Verify: crypto_aes_round maps to AesEnc idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round maps to AesEnc idiom")
step("Verify: crypto_aes_round maps to AesEnc idiom")
# @req: REQ-COMP-INTRINSIC-TO-TARGET-IDIOM-AARCH64-NAME-M-001
var result = intrinsic_to_target_idiom_aarch64("crypto_aes_round")
expect(result.is_some()).to_equal(true)
```

</details>

#### crypto_aes_round_last maps to AesEncLast idiom

- crypto_aes_round_last maps to AesEncLast idiom
- Verify: crypto_aes_round_last maps to AesEncLast idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round_last maps to AesEncLast idiom")
step("Verify: crypto_aes_round_last maps to AesEncLast idiom")
var result = intrinsic_to_target_idiom_aarch64("crypto_aes_round_last")
expect(result.is_some()).to_equal(true)
```

</details>

#### clmul_lo maps to ClmulLo idiom

- clmul_lo maps to ClmulLo idiom
- Verify: clmul_lo maps to ClmulLo idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_lo maps to ClmulLo idiom")
step("Verify: clmul_lo maps to ClmulLo idiom")
var result = intrinsic_to_target_idiom_aarch64("clmul_lo")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_popcount maps to Popcount idiom

- bit_popcount maps to Popcount idiom
- Verify: bit_popcount maps to Popcount idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_popcount maps to Popcount idiom")
step("Verify: bit_popcount maps to Popcount idiom")
var result = intrinsic_to_target_idiom_aarch64("bit_popcount")
expect(result.is_some()).to_equal(true)
```

</details>

<details>
<summary>Advanced: matrix_dot maps to MatrixDot idiom</summary>

#### matrix_dot maps to MatrixDot idiom

- matrix_dot maps to MatrixDot idiom
- Verify: matrix_dot maps to MatrixDot idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matrix_dot maps to MatrixDot idiom")
step("Verify: matrix_dot maps to MatrixDot idiom")
var result = intrinsic_to_target_idiom_aarch64("matrix_dot")
expect(result.is_some()).to_equal(true)
```

</details>


</details>

#### crypto_sha512_rnds2 maps to Sha512Rounds2 idiom

- crypto_sha512_rnds2 maps to Sha512Rounds2 idiom
- Verify: crypto_sha512_rnds2 maps to Sha512Rounds2 idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_rnds2 maps to Sha512Rounds2 idiom")
step("Verify: crypto_sha512_rnds2 maps to Sha512Rounds2 idiom")
var result = intrinsic_to_target_idiom_aarch64("crypto_sha512_rnds2")
expect(result.is_some()).to_equal(true)
```

</details>

#### crypto_sha512_msg1 maps to Sha512Msg1 idiom

- crypto_sha512_msg1 maps to Sha512Msg1 idiom
- Verify: crypto_sha512_msg1 maps to Sha512Msg1 idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_msg1 maps to Sha512Msg1 idiom")
step("Verify: crypto_sha512_msg1 maps to Sha512Msg1 idiom")
var result = intrinsic_to_target_idiom_aarch64("crypto_sha512_msg1")
expect(result.is_some()).to_equal(true)
```

</details>

#### crypto_sha512_msg2 maps to Sha512Msg2 idiom

- crypto_sha512_msg2 maps to Sha512Msg2 idiom
- Verify: crypto_sha512_msg2 maps to Sha512Msg2 idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_msg2 maps to Sha512Msg2 idiom")
step("Verify: crypto_sha512_msg2 maps to Sha512Msg2 idiom")
var result = intrinsic_to_target_idiom_aarch64("crypto_sha512_msg2")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_rotate_left maps to RotateLeft idiom

- bit_rotate_left maps to RotateLeft idiom
- Verify: bit_rotate_left maps to RotateLeft idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_left maps to RotateLeft idiom")
step("Verify: bit_rotate_left maps to RotateLeft idiom")
var result = intrinsic_to_target_idiom_aarch64("bit_rotate_left")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_rotate_right maps to RotateRight idiom

- bit_rotate_right maps to RotateRight idiom
- Verify: bit_rotate_right maps to RotateRight idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_right maps to RotateRight idiom")
step("Verify: bit_rotate_right maps to RotateRight idiom")
var result = intrinsic_to_target_idiom_aarch64("bit_rotate_right")
expect(result.is_some()).to_equal(true)
```

</details>

#### bit_parity maps to Parity idiom

- bit_parity maps to Parity idiom
- Verify: bit_parity maps to Parity idiom
   - Expected: result.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_parity maps to Parity idiom")
step("Verify: bit_parity maps to Parity idiom")
var result = intrinsic_to_target_idiom_aarch64("bit_parity")
expect(result.is_some()).to_equal(true)
```

</details>

#### unknown name returns nil

- unknown name returns nil
- Verify: unknown name returns nil
   - Expected: result.is_some() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown name returns nil")
step("Verify: unknown name returns nil")
var result = intrinsic_to_target_idiom_aarch64("not_a_real_intrinsic")
expect(result.is_some()).to_equal(false)
```

</details>

### lower_cipher_intrinsic_aarch64 — AES lowering with crypto caps

#### crypto_aes_round emits 8 bytes (AESE+AESMC pair)

- crypto_aes_round emits 8 bytes (AESE+AESMC pair)
- Verify: crypto_aes_round emits 8 bytes (AESE+AESMC pair)
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round emits 8 bytes (AESE+AESMC pair)")
step("Verify: crypto_aes_round emits 8 bytes (AESE+AESMC pair)")
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crypto_aes_round_last emits 4 bytes (AESE only)

- crypto_aes_round_last emits 4 bytes (AESE only)
- Verify: crypto_aes_round_last emits 4 bytes (AESE only)
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round_last emits 4 bytes (AESE only)")
step("Verify: crypto_aes_round_last emits 4 bytes (AESE only)")
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round_last", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crypto_aes_inv_round emits 8 bytes (AESD+AESIMC pair)

- crypto_aes_inv_round emits 8 bytes (AESD+AESIMC pair)
- Verify: crypto_aes_inv_round emits 8 bytes (AESD+AESIMC pair)
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_inv_round emits 8 bytes (AESD+AESIMC pair)")
step("Verify: crypto_aes_inv_round emits 8 bytes (AESD+AESIMC pair)")
var r = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crypto_aes_inv_round_last emits 4 bytes (AESD only)

- crypto_aes_inv_round_last emits 4 bytes (AESD only)
- Verify: crypto_aes_inv_round_last emits 4 bytes (AESD only)
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_inv_round_last emits 4 bytes (AESD only)")
step("Verify: crypto_aes_inv_round_last emits 4 bytes (AESD only)")
var r = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round_last", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

### lower_cipher_intrinsic_aarch64 — bare Aarch64Caps refuses cipher idioms

#### AES round on bare caps returns lowered=false, reason='no-cap'

- AES round on bare caps returns lowered=false, reason='no-cap'
- Verify: AES round on bare caps returns lowered=false, reason='no-cap'
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AES round on bare caps returns lowered=false, reason='no-cap'")
step("Verify: AES round on bare caps returns lowered=false, reason='no-cap'")
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0, 1], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### SHA256 rnds2 on bare caps refuses

- SHA256 rnds2 on bare caps refuses
- Verify: SHA256 rnds2 on bare caps refuses
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SHA256 rnds2 on bare caps refuses")
step("Verify: SHA256 rnds2 on bare caps refuses")
var r = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [0, 1, 2], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### CRC32_U8 on bare caps refuses

- CRC32_U8 on bare caps refuses
- Verify: CRC32_U8 on bare caps refuses
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32_U8 on bare caps refuses")
step("Verify: CRC32_U8 on bare caps refuses")
var r = lower_cipher_intrinsic_aarch64("crc32_u8", [0, 1, 2], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### CLMUL_LO on bare caps refuses

- CLMUL_LO on bare caps refuses
- Verify: CLMUL_LO on bare caps refuses
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CLMUL_LO on bare caps refuses")
step("Verify: CLMUL_LO on bare caps refuses")
var r = lower_cipher_intrinsic_aarch64("clmul_lo", [0, 1, 2], caps_bare())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

### lower_cipher_intrinsic_aarch64 — unknown name handling

#### unrecognised intrinsic returns lowered=false, reason='unknown'

- unrecognised intrinsic returns lowered=false, reason='unknown'
- Verify: unrecognised intrinsic returns lowered=false, reason='unknown'
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unrecognised intrinsic returns lowered=false, reason='unknown'")
step("Verify: unrecognised intrinsic returns lowered=false, reason='unknown'")
var r = lower_cipher_intrinsic_aarch64("not_a_real_intrinsic", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

#### empty name returns unknown

- empty name returns unknown
- Verify: empty name returns unknown
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("empty name returns unknown")
step("Verify: empty name returns unknown")
var r = lower_cipher_intrinsic_aarch64("", [], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

### lower_cipher_intrinsic_aarch64 — SHA256 / CRC32 / CLMUL on full caps

#### crypto_sha256_rnds2 emits 8 bytes (SHA256H+SHA256H2) when has_sha2

- crypto_sha256_rnds2 emits 8 bytes (SHA256H+SHA256H2) when has_sha2
- Verify: crypto_sha256_rnds2 emits 8 bytes (SHA256H+SHA256H2) when has_sha2
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha256_rnds2 emits 8 bytes (SHA256H+SHA256H2) when has_sha2")
step("Verify: crypto_sha256_rnds2 emits 8 bytes (SHA256H+SHA256H2) when has_sha2")
var r = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crc32_u8 lowers when has_crc32

- crc32_u8 lowers when has_crc32
- Verify: crc32_u8 lowers when has_crc32
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crc32_u8 lowers when has_crc32")
step("Verify: crc32_u8 lowers when has_crc32")
var r = lower_cipher_intrinsic_aarch64("crc32_u8", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crc32_u32 lowers when has_crc32

- crc32_u32 lowers when has_crc32
- Verify: crc32_u32 lowers when has_crc32
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crc32_u32 lowers when has_crc32")
step("Verify: crc32_u32 lowers when has_crc32")
var r = lower_cipher_intrinsic_aarch64("crc32_u32", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crc32_u64 lowers when has_crc32

- crc32_u64 lowers when has_crc32
- Verify: crc32_u64 lowers when has_crc32
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crc32_u64 lowers when has_crc32")
step("Verify: crc32_u64 lowers when has_crc32")
var r = lower_cipher_intrinsic_aarch64("crc32_u64", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### clmul_lo emits PMULL when has_pmull

- clmul_lo emits PMULL when has_pmull
- Verify: clmul_lo emits PMULL when has_pmull
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_lo emits PMULL when has_pmull")
step("Verify: clmul_lo emits PMULL when has_pmull")
var r = lower_cipher_intrinsic_aarch64("clmul_lo", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### clmul_hi emits PMULL2 when has_pmull

- clmul_hi emits PMULL2 when has_pmull
- Verify: clmul_hi emits PMULL2 when has_pmull
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_hi emits PMULL2 when has_pmull")
step("Verify: clmul_hi emits PMULL2 when has_pmull")
var r = lower_cipher_intrinsic_aarch64("clmul_hi", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

### lower_cipher_intrinsic_aarch64 — arity checking

#### crypto_aes_round with 3 args returns bad-arity

- crypto_aes_round with 3 args returns bad-arity
- Verify: crypto_aes_round with 3 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round with 3 args returns bad-arity")
step("Verify: crypto_aes_round with 3 args returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0, 1, 2], caps_aes_only())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### clmul_lo with 2 args returns bad-arity

- clmul_lo with 2 args returns bad-arity
- Verify: clmul_lo with 2 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_lo with 2 args returns bad-arity")
step("Verify: clmul_lo with 2 args returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("clmul_lo", [0, 1], caps_aes_only())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

### lower_cipher_intrinsic_aarch64 — portable bit/matrix scaffolding

#### bit_bswap lowers on capable caps

- bit_bswap lowers on capable caps
- Verify: bit_bswap lowers on capable caps
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bswap lowers on capable caps")
step("Verify: bit_bswap lowers on capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_bswap", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_clz lowers on capable caps

- bit_clz lowers on capable caps
- Verify: bit_clz lowers on capable caps
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_clz lowers on capable caps")
step("Verify: bit_clz lowers on capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_clz", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_ctz lowers on capable caps

- bit_ctz lowers on capable caps
- Verify: bit_ctz lowers on capable caps
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_ctz lowers on capable caps")
step("Verify: bit_ctz lowers on capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_ctz", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### bit_bitreverse lowers on sve2-capable caps

- bit_bitreverse lowers on sve2-capable caps
- Verify: bit_bitreverse lowers on sve2-capable caps
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bitreverse lowers on sve2-capable caps")
step("Verify: bit_bitreverse lowers on sve2-capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_bitreverse", [0, 1], caps_sve2())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_popcount stays on the current non-direct path on capable caps

- bit_popcount stays on the current non-direct path on capable caps
- Verify: bit_popcount stays on the current non-direct path on capable caps
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_popcount stays on the current non-direct path on capable caps")
step("Verify: bit_popcount stays on the current non-direct path on capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_popcount", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

#### bit_clz with 1 arg returns bad-arity

- bit_clz with 1 arg returns bad-arity
- Verify: bit_clz with 1 arg returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_clz with 1 arg returns bad-arity")
step("Verify: bit_clz with 1 arg returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("bit_clz", [0], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_ctz with 1 arg returns bad-arity

- bit_ctz with 1 arg returns bad-arity
- Verify: bit_ctz with 1 arg returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_ctz with 1 arg returns bad-arity")
step("Verify: bit_ctz with 1 arg returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("bit_ctz", [0], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_bitreverse with 1 arg returns bad-arity

- bit_bitreverse with 1 arg returns bad-arity
- Verify: bit_bitreverse with 1 arg returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bitreverse with 1 arg returns bad-arity")
step("Verify: bit_bitreverse with 1 arg returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("bit_bitreverse", [0], caps_sve2())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

<details>
<summary>Advanced: matrix_dot is recognised and returns unimplemented on capable caps</summary>

#### matrix_dot is recognised and returns unimplemented on capable caps

- matrix_dot is recognised and returns unimplemented on capable caps
- Verify: matrix_dot is recognised and returns unimplemented on capable caps
   - Expected: r.lowered is false
   - Expected: r.reason equals `unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matrix_dot is recognised and returns unimplemented on capable caps")
step("Verify: matrix_dot is recognised and returns unimplemented on capable caps")
var r = lower_cipher_intrinsic_aarch64("matrix_dot", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unimplemented")
```

</details>


</details>

### lower_cipher_intrinsic_aarch64 — SHA-512 lowering

#### crypto_sha512_rnds2 emits 8 bytes (SHA512H+SHA512H2) when has_sha512

- crypto_sha512_rnds2 emits 8 bytes (SHA512H+SHA512H2) when has_sha512
- Verify: crypto_sha512_rnds2 emits 8 bytes (SHA512H+SHA512H2) when has_sha512
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_rnds2 emits 8 bytes (SHA512H+SHA512H2) when has_sha512")
step("Verify: crypto_sha512_rnds2 emits 8 bytes (SHA512H+SHA512H2) when has_sha512")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_rnds2", [0, 1, 2], caps_sha512())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(8)
```

</details>

#### crypto_sha512_msg1 emits 4 bytes (SHA512SU0) when has_sha512

- crypto_sha512_msg1 emits 4 bytes (SHA512SU0) when has_sha512
- Verify: crypto_sha512_msg1 emits 4 bytes (SHA512SU0) when has_sha512
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_msg1 emits 4 bytes (SHA512SU0) when has_sha512")
step("Verify: crypto_sha512_msg1 emits 4 bytes (SHA512SU0) when has_sha512")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg1", [0, 1], caps_sha512())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crypto_sha512_msg2 emits 4 bytes (SHA512SU1) when has_sha512

- crypto_sha512_msg2 emits 4 bytes (SHA512SU1) when has_sha512
- Verify: crypto_sha512_msg2 emits 4 bytes (SHA512SU1) when has_sha512
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_msg2 emits 4 bytes (SHA512SU1) when has_sha512")
step("Verify: crypto_sha512_msg2 emits 4 bytes (SHA512SU1) when has_sha512")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg2", [0, 1, 2], caps_sha512())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### crypto_sha512_rnds2 on caps without has_sha512 returns no-cap

- crypto_sha512_rnds2 on caps without has_sha512 returns no-cap
- Verify: crypto_sha512_rnds2 on caps without has_sha512 returns no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_rnds2 on caps without has_sha512 returns no-cap")
step("Verify: crypto_sha512_rnds2 on caps without has_sha512 returns no-cap")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_rnds2", [0, 1, 2], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### crypto_sha512_msg1 on caps without has_sha512 returns no-cap

- crypto_sha512_msg1 on caps without has_sha512 returns no-cap
- Verify: crypto_sha512_msg1 on caps without has_sha512 returns no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_msg1 on caps without has_sha512 returns no-cap")
step("Verify: crypto_sha512_msg1 on caps without has_sha512 returns no-cap")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg1", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### crypto_sha512_rnds2 with 2 args returns bad-arity

- crypto_sha512_rnds2 with 2 args returns bad-arity
- Verify: crypto_sha512_rnds2 with 2 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_rnds2 with 2 args returns bad-arity")
step("Verify: crypto_sha512_rnds2 with 2 args returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_rnds2", [0, 1], caps_sha512())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### crypto_sha512_msg1 with 3 args returns bad-arity

- crypto_sha512_msg1 with 3 args returns bad-arity
- Verify: crypto_sha512_msg1 with 3 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_msg1 with 3 args returns bad-arity")
step("Verify: crypto_sha512_msg1 with 3 args returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg1", [0, 1, 2], caps_sha512())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### crypto_sha512_msg2 with 2 args returns bad-arity

- crypto_sha512_msg2 with 2 args returns bad-arity
- Verify: crypto_sha512_msg2 with 2 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha512_msg2 with 2 args returns bad-arity")
step("Verify: crypto_sha512_msg2 with 2 args returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("crypto_sha512_msg2", [0, 1], caps_sha512())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

### lower_cipher_intrinsic_aarch64 — rotate lowering

#### bit_rotate_right emits 4 bytes (EXTR/ROR) on capable caps

- bit_rotate_right emits 4 bytes (EXTR/ROR) on capable caps
- Verify: bit_rotate_right emits 4 bytes (EXTR/ROR) on capable caps
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_right emits 4 bytes (EXTR/ROR) on capable caps")
step("Verify: bit_rotate_right emits 4 bytes (EXTR/ROR) on capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_rotate_right", [0, 1, 7], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_rotate_left emits 4 bytes (EXTR/ROR neg) on capable caps

- bit_rotate_left emits 4 bytes (EXTR/ROR neg) on capable caps
- Verify: bit_rotate_left emits 4 bytes (EXTR/ROR neg) on capable caps
   - Expected: r.lowered is true
   - Expected: r.bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_left emits 4 bytes (EXTR/ROR neg) on capable caps")
step("Verify: bit_rotate_left emits 4 bytes (EXTR/ROR neg) on capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_rotate_left", [0, 1, 7], caps_full_crypto())
expect(r.lowered).to_equal(true)
expect(r.bytes.len()).to_equal(4)
```

</details>

#### bit_rotate_right with 2 args returns bad-arity

- bit_rotate_right with 2 args returns bad-arity
- Verify: bit_rotate_right with 2 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_right with 2 args returns bad-arity")
step("Verify: bit_rotate_right with 2 args returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("bit_rotate_right", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_rotate_left with 2 args returns bad-arity

- bit_rotate_left with 2 args returns bad-arity
- Verify: bit_rotate_left with 2 args returns bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_left with 2 args returns bad-arity")
step("Verify: bit_rotate_left with 2 args returns bad-arity")
var r = lower_cipher_intrinsic_aarch64("bit_rotate_left", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

### lower_cipher_intrinsic_aarch64 — parity lowering

#### bit_parity returns unimplemented on capable caps

- bit_parity returns unimplemented on capable caps
- Verify: bit_parity returns unimplemented on capable caps
   - Expected: r.lowered is false
   - Expected: r.reason equals `unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_parity returns unimplemented on capable caps")
step("Verify: bit_parity returns unimplemented on capable caps")
var r = lower_cipher_intrinsic_aarch64("bit_parity", [0, 1], caps_full_crypto())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unimplemented")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-INTRINSIC-TO-TARGET-IDIOM-AARCH64-NAME-M-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b3b9dd88c7df2884dc584e07f9097dc032d2416e7ba8fad1f755cbd770083777`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3b9dd88c7df2884dc584e07f9097dc032d2416e7ba8fad1f755cbd770083777`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3b9dd88c7df2884dc584e07f9097dc032d2416e7ba8fad1f755cbd770083777`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_round maps to AesEnc idiom' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_round_last maps to AesEncLast idiom' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/intrinsic_lowering_aarch64_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clmul_lo maps to ClmulLo idiom' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
