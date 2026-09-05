# Intrinsic Lowering Riscv Specification

> Tests covering intrinsic_lowering_riscv — name to TargetIdiom, intrinsic_lowering_riscv — full caps byte results, intrinsic_lowering_riscv — no-cap cases, intrinsic_lowering_riscv — unknown intrinsic, intrinsic_lowering_riscv — bad arity, intrinsic_lowering_riscv — matrix scaffolding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intrinsic Lowering Riscv Specification

## Scenarios

### intrinsic_lowering_riscv — name to TargetIdiom

#### crypto_aes_round maps to AesEnc

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- crypto_aes_round maps to AesEnc
   - Expected: idiom equals `TargetIdiom.AesEnc`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round maps to AesEnc")
var result = intrinsic_to_target_idiom_riscv("crypto_aes_round")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.AesEnc)
    case _:
        expect(0).to_equal(1)
```

</details>

#### crypto_aes_round_last maps to AesEncLast

- crypto_aes_round_last maps to AesEncLast
   - Expected: idiom equals `TargetIdiom.AesEncLast`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round_last maps to AesEncLast")
var result = intrinsic_to_target_idiom_riscv("crypto_aes_round_last")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.AesEncLast)
    case _:
        expect(0).to_equal(1)
```

</details>

#### crypto_aes_inv_round maps to AesDec

- crypto_aes_inv_round maps to AesDec
   - Expected: idiom equals `TargetIdiom.AesDec`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_inv_round maps to AesDec")
var result = intrinsic_to_target_idiom_riscv("crypto_aes_inv_round")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.AesDec)
    case _:
        expect(0).to_equal(1)
```

</details>

#### crypto_aes_inv_round_last maps to AesDecLast

- crypto_aes_inv_round_last maps to AesDecLast
   - Expected: idiom equals `TargetIdiom.AesDecLast`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_inv_round_last maps to AesDecLast")
var result = intrinsic_to_target_idiom_riscv("crypto_aes_inv_round_last")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.AesDecLast)
    case _:
        expect(0).to_equal(1)
```

</details>

#### crypto_sha256_rnds2 maps to Sha256Rounds2

- crypto_sha256_rnds2 maps to Sha256Rounds2
   - Expected: idiom equals `TargetIdiom.Sha256Rounds2`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha256_rnds2 maps to Sha256Rounds2")
var result = intrinsic_to_target_idiom_riscv("crypto_sha256_rnds2")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.Sha256Rounds2)
    case _:
        expect(0).to_equal(1)
```

</details>

#### clmul_lo maps to ClmulLo

- clmul_lo maps to ClmulLo
   - Expected: idiom equals `TargetIdiom.ClmulLo`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_lo maps to ClmulLo")
var result = intrinsic_to_target_idiom_riscv("clmul_lo")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.ClmulLo)
    case _:
        expect(0).to_equal(1)
```

</details>

#### clmul_hi maps to ClmulHi

- clmul_hi maps to ClmulHi
   - Expected: idiom equals `TargetIdiom.ClmulHi`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_hi maps to ClmulHi")
var result = intrinsic_to_target_idiom_riscv("clmul_hi")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.ClmulHi)
    case _:
        expect(0).to_equal(1)
```

</details>

#### bit_popcount maps to Popcount

- bit_popcount maps to Popcount
   - Expected: idiom equals `TargetIdiom.Popcount`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_popcount maps to Popcount")
var result = intrinsic_to_target_idiom_riscv("bit_popcount")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.Popcount)
    case _:
        expect(0).to_equal(1)
```

</details>

<details>
<summary>Advanced: matrix_dot maps to MatrixDot</summary>

#### matrix_dot maps to MatrixDot

- matrix_dot maps to MatrixDot
   - Expected: idiom equals `TargetIdiom.MatrixDot`
   - Expected: 0 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matrix_dot maps to MatrixDot")
var result = intrinsic_to_target_idiom_riscv("matrix_dot")
match result:
    case Some(idiom):
        expect(idiom).to_equal(TargetIdiom.MatrixDot)
    case _:
        expect(0).to_equal(1)
```

</details>


</details>

#### unknown name returns nil

- unknown name returns nil
   - Expected: 0 equals `1`
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown name returns nil")
var result = intrinsic_to_target_idiom_riscv("not_a_real_intrinsic")
match result:
    case Some(_):
        expect(0).to_equal(1)
    case _:
        expect(1).to_equal(1)
```

</details>

### intrinsic_lowering_riscv — full caps byte results

#### crypto_aes_round lowered with 2 args

- crypto_aes_round lowered with 2 args
   - Expected: r.lowered is true
   - Expected: r.bytes.length equals `4`
   - Expected: r.bytes[0] equals `0xD7`
   - Expected: r.bytes[3] equals `0xA6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round lowered with 2 args")
# vaesem.vv v1,v2 → [0xD7,0x20,0x20,0xA6]
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("crypto_aes_round", args, full_caps())
expect(r.lowered).to_equal(true)
expect(r.bytes.length).to_equal(4)
expect(r.bytes[0]).to_equal(0xD7)
expect(r.bytes[3]).to_equal(0xA6)
```

</details>

#### crypto_aes_round_last → vaesef.vv bytes

- crypto_aes_round_last → vaesef.vv bytes
   - Expected: r.lowered is true
   - Expected: r.bytes.length equals `4`
   - Expected: r.bytes[3] equals `0xA2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round_last → vaesef.vv bytes")
# vaesef.vv v1,v2 → [0xD7,0x20,0x20,0xA2]
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("crypto_aes_round_last", args, full_caps())
expect(r.lowered).to_equal(true)
expect(r.bytes.length).to_equal(4)
expect(r.bytes[3]).to_equal(0xA2)
```

</details>

#### crypto_aes_inv_round → vaesdm.vv bytes

- crypto_aes_inv_round → vaesdm.vv bytes
   - Expected: r.lowered is true
   - Expected: r.bytes.length equals `4`
   - Expected: r.bytes[3] equals `0xAE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_inv_round → vaesdm.vv bytes")
# vaesdm.vv v1,v2 → [0xD7,0x20,0x20,0xAE]
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("crypto_aes_inv_round", args, full_caps())
expect(r.lowered).to_equal(true)
expect(r.bytes.length).to_equal(4)
expect(r.bytes[3]).to_equal(0xAE)
```

</details>

#### crypto_aes_inv_round_last → vaesdf.vv bytes

- crypto_aes_inv_round_last → vaesdf.vv bytes
   - Expected: r.lowered is true
   - Expected: r.bytes.length equals `4`
   - Expected: r.bytes[3] equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_inv_round_last → vaesdf.vv bytes")
# vaesdf.vv v1,v2 → [0xD7,0x20,0x20,0xAA]
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("crypto_aes_inv_round_last", args, full_caps())
expect(r.lowered).to_equal(true)
expect(r.bytes.length).to_equal(4)
expect(r.bytes[3]).to_equal(0xAA)
```

</details>

#### crypto_sha256_rnds2 → vsha2cl.vv + vsha2ch.vv (8 bytes)

- crypto_sha256_rnds2 → vsha2cl.vv + vsha2ch.vv (8 bytes)
   - Expected: r.lowered is true
   - Expected: r.bytes.length equals `8`
   - Expected: r.bytes[0] equals `0xD7`
   - Expected: r.bytes[3] equals `0xBE`
   - Expected: r.bytes[4] equals `0xD7`
   - Expected: r.bytes[7] equals `0xBA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha256_rnds2 → vsha2cl.vv + vsha2ch.vv (8 bytes)")
# vsha2cl.vv v1,v2,v3 + vsha2ch.vv v1,v2,v3
var args: [i64] = [1, 2, 3]
var r = lower_cipher_intrinsic_riscv("crypto_sha256_rnds2", args, full_caps())
expect(r.lowered).to_equal(true)
expect(r.bytes.length).to_equal(8)
# First 4 bytes: vsha2cl.vv → byte[3]=0xBE
expect(r.bytes[0]).to_equal(0xD7)
expect(r.bytes[3]).to_equal(0xBE)
# Next 4 bytes: vsha2ch.vv → byte[3]=0xBA
expect(r.bytes[4]).to_equal(0xD7)
expect(r.bytes[7]).to_equal(0xBA)
```

</details>

#### clmul_lo → vghsh.vv bytes

- clmul_lo → vghsh.vv bytes
   - Expected: r.lowered is true
   - Expected: r.bytes.length equals `4`
   - Expected: r.bytes[3] equals `0xB2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_lo → vghsh.vv bytes")
# vghsh.vv v1,v2,v3 → [0xD7,0xA0,0x21,0xB2]
var args: [i64] = [1, 2, 3]
var r = lower_cipher_intrinsic_riscv("clmul_lo", args, full_caps())
expect(r.lowered).to_equal(true)
expect(r.bytes.length).to_equal(4)
expect(r.bytes[3]).to_equal(0xB2)
```

</details>

#### clmul_hi → vgmul.vv bytes

- clmul_hi → vgmul.vv bytes
   - Expected: r.lowered is true
   - Expected: r.bytes.length equals `4`
   - Expected: r.bytes[3] equals `0xA6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_hi → vgmul.vv bytes")
# vgmul.vv v1,v2 → [0xD7,0x20,0x20,0xA6]
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("clmul_hi", args, full_caps())
expect(r.lowered).to_equal(true)
expect(r.bytes.length).to_equal(4)
expect(r.bytes[3]).to_equal(0xA6)
```

</details>

#### bit_rotate_left lowers to rol bytes

- bit_rotate_left lowers to rol bytes
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[179, 16, 49, 96]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_left lowers to rol bytes")
# rol rd=1, rs1=2, rs2=3 — Zbb: funct7=0x30, funct3=0x1
var r = lower_cipher_intrinsic_riscv("bit_rotate_left", [1, 2, 3], scalar_zbb_caps())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([179, 16, 49, 96])
```

</details>

#### bit_rotate_right lowers to ror bytes via zbkb

- bit_rotate_right lowers to ror bytes via zbkb
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[179, 80, 49, 96]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_right lowers to ror bytes via zbkb")
# ror rd=1, rs1=2, rs2=3 — Zbkb: funct7=0x30, funct3=0x5
var r = lower_cipher_intrinsic_riscv("bit_rotate_right", [1, 2, 3], scalar_zbkb_only_caps())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([179, 80, 49, 96])
```

</details>

#### bit_clz lowers to clz bytes

- bit_clz lowers to clz bytes
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[147, 16, 1, 96]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_clz lowers to clz bytes")
var r = lower_cipher_intrinsic_riscv("bit_clz", [1, 2], scalar_zbb_caps())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([147, 16, 1, 96])
```

</details>

#### bit_ctz lowers to ctz bytes

- bit_ctz lowers to ctz bytes
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[147, 16, 17, 96]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_ctz lowers to ctz bytes")
var r = lower_cipher_intrinsic_riscv("bit_ctz", [1, 2], scalar_zbb_caps())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([147, 16, 17, 96])
```

</details>

#### bit_popcount lowers to cpop bytes

- bit_popcount lowers to cpop bytes
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[147, 16, 33, 96]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_popcount lowers to cpop bytes")
var r = lower_cipher_intrinsic_riscv("bit_popcount", [1, 2], scalar_zbb_caps())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([147, 16, 33, 96])
```

</details>

#### bit_bswap lowers to rev8 bytes

- bit_bswap lowers to rev8 bytes
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[147, 80, 129, 107]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bswap lowers to rev8 bytes")
var r = lower_cipher_intrinsic_riscv("bit_bswap", [1, 2], scalar_zbb_caps())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([147, 80, 129, 107])
```

</details>

#### bit_bitreverse lowers to brev8 + rev8 bytes

- bit_bitreverse lowers to brev8 + rev8 bytes
   - Expected: r.lowered is true
   - Expected: r.reason equals ``
   - Expected: r.bytes equals `[147, 87, 120, 104, 147, 87, 136, 107]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bitreverse lowers to brev8 + rev8 bytes")
var r = lower_cipher_intrinsic_riscv("bit_bitreverse", [15, 16], scalar_full_bitmanip_caps())
expect(r.lowered).to_equal(true)
expect(r.reason).to_equal("")
expect(r.bytes).to_equal([147, 87, 120, 104, 147, 87, 136, 107])
```

</details>

### intrinsic_lowering_riscv — no-cap cases

#### crypto_aes_round with bare caps → no-cap

- crypto_aes_round with bare caps → no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round with bare caps → no-cap")
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("crypto_aes_round", args, bare_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### crypto_sha256_rnds2 with aes_only caps → no-cap

- crypto_sha256_rnds2 with aes_only caps → no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha256_rnds2 with aes_only caps → no-cap")
var args: [i64] = [1, 2, 3]
var r = lower_cipher_intrinsic_riscv("crypto_sha256_rnds2", args, aes_only_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### clmul_lo with aes_only caps → no-cap

- clmul_lo with aes_only caps → no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_lo with aes_only caps → no-cap")
var args: [i64] = [1, 2, 3]
var r = lower_cipher_intrinsic_riscv("clmul_lo", args, aes_only_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### clmul_hi with bare caps → no-cap

- clmul_hi with bare caps → no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_hi with bare caps → no-cap")
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("clmul_hi", args, bare_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_popcount with zbkb-only caps → no-cap

- bit_popcount with zbkb-only caps → no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_popcount with zbkb-only caps → no-cap")
var r = lower_cipher_intrinsic_riscv("bit_popcount", [1, 2], scalar_zbkb_only_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

#### bit_bitreverse with zbb-only caps → no-cap

- bit_bitreverse with zbb-only caps → no-cap
   - Expected: r.lowered is false
   - Expected: r.reason equals `no-cap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bitreverse with zbb-only caps → no-cap")
var r = lower_cipher_intrinsic_riscv("bit_bitreverse", [1, 2], scalar_zbb_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("no-cap")
```

</details>

### intrinsic_lowering_riscv — unknown intrinsic

#### unknown name returns reason=unknown

- unknown name returns reason=unknown
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown name returns reason=unknown")
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("crypto_does_not_exist", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

#### empty name returns reason=unknown

- empty name returns reason=unknown
   - Expected: r.lowered is false
   - Expected: r.reason equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("empty name returns reason=unknown")
var args: [i64] = []
var r = lower_cipher_intrinsic_riscv("", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unknown")
```

</details>

### intrinsic_lowering_riscv — bad arity

#### crypto_aes_round with 0 args → bad-arity

- crypto_aes_round with 0 args → bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round with 0 args → bad-arity")
var args: [i64] = []
var r = lower_cipher_intrinsic_riscv("crypto_aes_round", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### crypto_aes_round with 3 args → bad-arity

- crypto_aes_round with 3 args → bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_aes_round with 3 args → bad-arity")
var args: [i64] = [1, 2, 3]
var r = lower_cipher_intrinsic_riscv("crypto_aes_round", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### crypto_sha256_rnds2 with 2 args → bad-arity

- crypto_sha256_rnds2 with 2 args → bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("crypto_sha256_rnds2 with 2 args → bad-arity")
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("crypto_sha256_rnds2", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### clmul_lo with 2 args → bad-arity

- clmul_lo with 2 args → bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_lo with 2 args → bad-arity")
var args: [i64] = [1, 2]
var r = lower_cipher_intrinsic_riscv("clmul_lo", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### clmul_hi with 3 args → bad-arity

- clmul_hi with 3 args → bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("clmul_hi with 3 args → bad-arity")
var args: [i64] = [1, 2, 3]
var r = lower_cipher_intrinsic_riscv("clmul_hi", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_rotate_left with 2 args → bad-arity

- bit_rotate_left with 2 args → bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_rotate_left with 2 args → bad-arity")
var r = lower_cipher_intrinsic_riscv("bit_rotate_left", [1, 2], scalar_zbb_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_bswap with 1 arg -> bad-arity

- bit_bswap with 1 arg -> bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bswap with 1 arg -> bad-arity")
var r = lower_cipher_intrinsic_riscv("bit_bswap", [1], scalar_zbb_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_clz with 1 arg -> bad-arity

- bit_clz with 1 arg -> bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_clz with 1 arg -> bad-arity")
var r = lower_cipher_intrinsic_riscv("bit_clz", [1], scalar_zbb_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_ctz with 1 arg -> bad-arity

- bit_ctz with 1 arg -> bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_ctz with 1 arg -> bad-arity")
var r = lower_cipher_intrinsic_riscv("bit_ctz", [1], scalar_zbb_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_popcount with 1 arg -> bad-arity

- bit_popcount with 1 arg -> bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_popcount with 1 arg -> bad-arity")
var r = lower_cipher_intrinsic_riscv("bit_popcount", [1], scalar_zbb_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

#### bit_bitreverse with 1 arg -> bad-arity

- bit_bitreverse with 1 arg -> bad-arity
   - Expected: r.lowered is false
   - Expected: r.reason equals `bad-arity`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bit_bitreverse with 1 arg -> bad-arity")
var r = lower_cipher_intrinsic_riscv("bit_bitreverse", [1], scalar_full_bitmanip_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("bad-arity")
```

</details>

### intrinsic_lowering_riscv — matrix scaffolding

<details>
<summary>Advanced: matrix_dot is recognised and returns unimplemented on capable caps</summary>

#### matrix_dot is recognised and returns unimplemented on capable caps

- matrix_dot is recognised and returns unimplemented on capable caps
   - Expected: r.lowered is false
   - Expected: r.reason equals `unimplemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matrix_dot is recognised and returns unimplemented on capable caps")
var args: [i64] = [1, 2, 3]
var r = lower_cipher_intrinsic_riscv("matrix_dot", args, full_caps())
expect(r.lowered).to_equal(false)
expect(r.reason).to_equal("unimplemented")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering intrinsic_lowering_riscv — name to TargetIdiom, intrinsic_lowering_riscv — full caps byte results, intrinsic_lowering_riscv — no-cap cases, intrinsic_lowering_riscv — unknown intrinsic, intrinsic_lowering_riscv — bad arity, intrinsic_lowering_riscv — matrix scaffolding.
- intrinsic_lowering_riscv — name to TargetIdiom
- intrinsic_lowering_riscv — full caps byte results
- intrinsic_lowering_riscv — no-cap cases
- intrinsic_lowering_riscv — unknown intrinsic
- intrinsic_lowering_riscv — bad arity
- intrinsic_lowering_riscv — matrix scaffolding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `623af170830c01006a02eefdeaf91e309cbe80a4b41cf81b079e871239e82d61`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `623af170830c01006a02eefdeaf91e309cbe80a4b41cf81b079e871239e82d61`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `623af170830c01006a02eefdeaf91e309cbe80a4b41cf81b079e871239e82d61`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_round maps to AesEnc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_round_last maps to AesEncLast' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/intrinsic_lowering_riscv_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crypto_aes_inv_round maps to AesDec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
