# Lowering X86 Crypto Specification

> <details>

<!-- sdn-diagram:id=lowering_x86_crypto_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lowering_x86_crypto_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lowering_x86_crypto_spec -> std
lowering_x86_crypto_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lowering_x86_crypto_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lowering X86 Crypto Specification

## Scenarios

### x86 cipher intrinsic lowering — AES-NI

#### AESENC xmm0,xmm1 (crypto_aes_round [0,1])

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f38dcc1")
```

</details>

#### AESENC output length is 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crypto_aes_round", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

#### AESENCLAST xmm0,xmm1 (crypto_aes_round_last [0,1])

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crypto_aes_round_last", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f38ddc1")
```

</details>

#### AESENCLAST output length is 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crypto_aes_round_last", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

#### AESDEC xmm2,xmm3 (crypto_aes_inv_round [2,3])

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crypto_aes_inv_round", [2, 3], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f38ded3")
```

</details>

#### AESDEC output length is 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crypto_aes_inv_round", [2, 3], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

### x86 cipher intrinsic lowering — CRC32

#### CRC32 r32,r8 (crc32_u8 [0,1])

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crc32_u8", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("f20f38f0c1")
```

</details>

#### CRC32 r32,r8 output length is 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crc32_u8", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(5)
```

</details>

#### CRC32 r64,r64 with REX.W (crc32_u64 [0,0])

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crc32_u64", [0, 0], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("f2480f38f1c0")
```

</details>

#### CRC32 r64,r64 output length is 6 bytes (REX prefix)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("crc32_u64", [0, 0], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(6)
```

</details>

### x86 cipher intrinsic lowering — PCLMULQDQ

#### PCLMULQDQ xmm0,xmm1,0x00 (clmul_lo [0,1])

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("clmul_lo", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f3a44c100")
```

</details>

#### PCLMULQDQ clmul_lo output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("clmul_lo", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(6)
```

</details>

#### PCLMULQDQ xmm0,xmm1,0x11 (clmul_hi [0,1])

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("clmul_hi", [0, 1], TEST_X86_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("660f3a44c111")
```

</details>

#### PCLMULQDQ clmul_hi output length is 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("clmul_hi", [0, 1], TEST_X86_CAPS)
expect(result.bytes.len()).to_equal(6)
```

</details>

### x86 cipher intrinsic lowering — failure cases

#### unknown intrinsic name returns lowered=false, reason=unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_x86("sha_not_real", [0, 1], TEST_X86_CAPS)
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
val result = lower_cipher_intrinsic_x86("crypto_aes_round", [0], TEST_X86_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/lowering_x86_crypto_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86 cipher intrinsic lowering — AES-NI
- x86 cipher intrinsic lowering — CRC32
- x86 cipher intrinsic lowering — PCLMULQDQ
- x86 cipher intrinsic lowering — failure cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
