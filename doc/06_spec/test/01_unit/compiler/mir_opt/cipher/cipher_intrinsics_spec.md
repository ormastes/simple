# Cipher Intrinsics Specification

> <details>

<!-- sdn-diagram:id=cipher_intrinsics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cipher_intrinsics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cipher_intrinsics_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cipher_intrinsics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cipher Intrinsics Specification

## Scenarios

### cipher intrinsic name constants — AES

#### CRYPTO_AES_ROUND is 'crypto_aes_round'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_AES_ROUND).to_equal("crypto_aes_round")
```

</details>

#### CRYPTO_AES_ROUND_LAST is 'crypto_aes_round_last'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_AES_ROUND_LAST).to_equal("crypto_aes_round_last")
```

</details>

#### CRYPTO_AES_INV_ROUND is 'crypto_aes_inv_round'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_AES_INV_ROUND).to_equal("crypto_aes_inv_round")
```

</details>

#### CRYPTO_AES_INV_ROUND_LAST is 'crypto_aes_inv_round_last'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_AES_INV_ROUND_LAST).to_equal("crypto_aes_inv_round_last")
```

</details>

#### CRYPTO_AES_IMC is 'crypto_aes_imc'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_AES_IMC).to_equal("crypto_aes_imc")
```

</details>

#### CRYPTO_AES_KEYGEN_ASSIST is 'crypto_aes_keygen_assist'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_AES_KEYGEN_ASSIST).to_equal("crypto_aes_keygen_assist")
```

</details>

### cipher intrinsic name constants — SHA-256

#### CRYPTO_SHA256_RNDS2 is 'crypto_sha256_rounds2'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_SHA256_RNDS2).to_equal("crypto_sha256_rounds2")
```

</details>

#### CRYPTO_SHA256_MSG1 is 'crypto_sha256_msg1'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_SHA256_MSG1).to_equal("crypto_sha256_msg1")
```

</details>

#### CRYPTO_SHA256_MSG2 is 'crypto_sha256_msg2'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRYPTO_SHA256_MSG2).to_equal("crypto_sha256_msg2")
```

</details>

### cipher intrinsic name constants — CRC32 / CLMUL

#### CRC32_U8 is 'crc32_u8'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRC32_U8).to_equal("crc32_u8")
```

</details>

#### CRC32_U32 is 'crc32_u32'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRC32_U32).to_equal("crc32_u32")
```

</details>

#### CRC32_U64 is 'crc32_u64'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CRC32_U64).to_equal("crc32_u64")
```

</details>

#### CLMUL_LO is 'clmul_lo'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CLMUL_LO).to_equal("clmul_lo")
```

</details>

#### CLMUL_HI is 'clmul_hi'

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CLMUL_HI).to_equal("clmul_hi")
```

</details>

### cipher_intrinsic_arg_count — known names return correct arity

#### AES round / round_last / inv variants take 2 args (state, round_key)

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count(CRYPTO_AES_ROUND).unwrap()).to_equal(2)
expect(cipher_intrinsic_arg_count(CRYPTO_AES_ROUND_LAST).unwrap()).to_equal(2)
expect(cipher_intrinsic_arg_count(CRYPTO_AES_INV_ROUND).unwrap()).to_equal(2)
expect(cipher_intrinsic_arg_count(CRYPTO_AES_INV_ROUND_LAST).unwrap()).to_equal(2)
```

</details>

#### AES IMC takes 1 arg (state only)

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count(CRYPTO_AES_IMC).unwrap()).to_equal(1)
```

</details>

#### AES keygen assist takes 2 args (state, rcon)

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count(CRYPTO_AES_KEYGEN_ASSIST).unwrap()).to_equal(2)
```

</details>

#### SHA256 rounds2 takes 3 args (a_state, b_state, w_k)

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count(CRYPTO_SHA256_RNDS2).unwrap()).to_equal(3)
```

</details>

#### SHA256 msg1 / msg2 each take 2 args

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count(CRYPTO_SHA256_MSG1).unwrap()).to_equal(2)
expect(cipher_intrinsic_arg_count(CRYPTO_SHA256_MSG2).unwrap()).to_equal(2)
```

</details>

#### CRC32 variants each take 2 args (crc, data)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count(CRC32_U8).unwrap()).to_equal(2)
expect(cipher_intrinsic_arg_count(CRC32_U32).unwrap()).to_equal(2)
expect(cipher_intrinsic_arg_count(CRC32_U64).unwrap()).to_equal(2)
```

</details>

#### CLMUL lo / hi each take 2 args

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count(CLMUL_LO).unwrap()).to_equal(2)
expect(cipher_intrinsic_arg_count(CLMUL_HI).unwrap()).to_equal(2)
```

</details>

### cipher_intrinsic_arg_count — unknown names return nil

#### empty string returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count("").?).to_equal(false)
```

</details>

#### non-cipher intrinsic 'simd_load_f32x4' returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count("simd_load_f32x4").?).to_equal(false)
```

</details>

#### typo'd 'crypto_aes_rounds' (extra s) returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cipher_intrinsic_arg_count("crypto_aes_rounds").?).to_equal(false)
```

</details>

### is_cipher_intrinsic — true for every registered name

#### AES family

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cipher_intrinsic(CRYPTO_AES_ROUND)).to_equal(true)
expect(is_cipher_intrinsic(CRYPTO_AES_ROUND_LAST)).to_equal(true)
expect(is_cipher_intrinsic(CRYPTO_AES_INV_ROUND)).to_equal(true)
expect(is_cipher_intrinsic(CRYPTO_AES_INV_ROUND_LAST)).to_equal(true)
expect(is_cipher_intrinsic(CRYPTO_AES_IMC)).to_equal(true)
expect(is_cipher_intrinsic(CRYPTO_AES_KEYGEN_ASSIST)).to_equal(true)
```

</details>

#### SHA-256 family

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cipher_intrinsic(CRYPTO_SHA256_RNDS2)).to_equal(true)
expect(is_cipher_intrinsic(CRYPTO_SHA256_MSG1)).to_equal(true)
expect(is_cipher_intrinsic(CRYPTO_SHA256_MSG2)).to_equal(true)
```

</details>

#### CRC32 + CLMUL family

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cipher_intrinsic(CRC32_U8)).to_equal(true)
expect(is_cipher_intrinsic(CRC32_U32)).to_equal(true)
expect(is_cipher_intrinsic(CRC32_U64)).to_equal(true)
expect(is_cipher_intrinsic(CLMUL_LO)).to_equal(true)
expect(is_cipher_intrinsic(CLMUL_HI)).to_equal(true)
```

</details>

### is_cipher_intrinsic — false for non-cipher names

#### empty string

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cipher_intrinsic("")).to_equal(false)
```

</details>

#### simd intrinsic

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cipher_intrinsic("simd_load_f32x4")).to_equal(false)
```

</details>

#### typo

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_cipher_intrinsic("crypto_aes_rounds")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/cipher/cipher_intrinsics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cipher intrinsic name constants — AES
- cipher intrinsic name constants — SHA-256
- cipher intrinsic name constants — CRC32 / CLMUL
- cipher_intrinsic_arg_count — known names return correct arity
- cipher_intrinsic_arg_count — unknown names return nil
- is_cipher_intrinsic — true for every registered name
- is_cipher_intrinsic — false for non-cipher names

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
