# Lowering Aarch64 Crypto Specification

> <details>

<!-- sdn-diagram:id=lowering_aarch64_crypto_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lowering_aarch64_crypto_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lowering_aarch64_crypto_spec -> std
lowering_aarch64_crypto_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lowering_aarch64_crypto_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lowering Aarch64 Crypto Specification

## Scenarios

### AArch64 cipher intrinsic lowering — AES encrypt rounds

#### AESE+AESMC V1,V2 (crypto_aes_round [1,2]) — full encrypt round (8 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4148284e2168284e")
```

</details>

#### crypto_aes_round output length is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(8)
```

</details>

#### AESE V1,V2 (crypto_aes_round_last [1,2]) — final encrypt round (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4148284e")
```

</details>

#### crypto_aes_round_last output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — AES decrypt rounds

#### AESD+AESIMC V1,V2 (crypto_aes_inv_round [1,2]) — full decrypt round (8 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4158284e2178284e")
```

</details>

#### crypto_aes_inv_round output length is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(8)
```

</details>

#### AESD V1,V2 (crypto_aes_inv_round_last [1,2]) — final decrypt round (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4158284e")
```

</details>

#### crypto_aes_inv_round_last output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_inv_round_last", [1, 2], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — SHA-256

#### SHA256H+SHA256H2 Q1,Q2,V3 (crypto_sha256_rnds2 [1,2,3]) — sha2 rounds (8 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4140035e4150035e")
```

</details>

#### crypto_sha256_rnds2 output length is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(8)
```

</details>

### AArch64 cipher intrinsic lowering — CRC32

#### CRC32B W1,W2,W3 (crc32_u8 [1,2,3]) — byte accumulate (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crc32_u8", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4140c31a")
```

</details>

#### crc32_u8 output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crc32_u8", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### CRC32W W1,W2,W3 (crc32_u32 [1,2,3]) — word accumulate (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crc32_u32", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("4148c31a")
```

</details>

#### crc32_u32 output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crc32_u32", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### CRC32X W1,W2,X3 (crc32_u64 [1,2,3]) — doubleword accumulate (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crc32_u64", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("414cc39a")
```

</details>

#### crc32_u64 output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crc32_u64", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — CLMUL (PMULL)

#### PMULL V1.1Q,V2.1D,V3.1D (clmul_lo [1,2,3]) — polynomial multiply low (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("clmul_lo", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("41e0e30e")
```

</details>

#### clmul_lo output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("clmul_lo", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### PMULL2 V1.1Q,V2.2D,V3.2D (clmul_hi [1,2,3]) — polynomial multiply high (4 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("clmul_hi", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("41e0e34e")
```

</details>

#### clmul_hi output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("clmul_hi", [1, 2, 3], TEST_AARCH64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### AArch64 cipher intrinsic lowering — failure cases

#### unknown intrinsic returns lowered=false, reason=unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("unknown_intrinsic", [0, 0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("unknown")
```

</details>

#### crypto_aes_round with 1 arg returns lowered=false, reason=bad-arity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_aes_round", [0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

#### crypto_sha256_rnds2 with 2 args returns lowered=false, reason=bad-arity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crypto_sha256_rnds2", [0, 0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

#### crc32_u8 with 2 args returns lowered=false, reason=bad-arity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_aarch64("crc32_u8", [0, 0], TEST_AARCH64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/lowering_aarch64_crypto_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AArch64 cipher intrinsic lowering — AES encrypt rounds
- AArch64 cipher intrinsic lowering — AES decrypt rounds
- AArch64 cipher intrinsic lowering — SHA-256
- AArch64 cipher intrinsic lowering — CRC32
- AArch64 cipher intrinsic lowering — CLMUL (PMULL)
- AArch64 cipher intrinsic lowering — failure cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
