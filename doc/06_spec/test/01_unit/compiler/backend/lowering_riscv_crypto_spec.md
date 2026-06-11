# Lowering Riscv Crypto Specification

> <details>

<!-- sdn-diagram:id=lowering_riscv_crypto_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lowering_riscv_crypto_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lowering_riscv_crypto_spec -> std
lowering_riscv_crypto_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lowering_riscv_crypto_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lowering Riscv Crypto Specification

## Scenarios

### RV64 Zvk cipher intrinsic lowering — AES rounds

#### vaesem.vv v1,v2 (crypto_aes_round [1,2]) — mid-round encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_round", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020a6")
```

</details>

#### vaesem.vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_round", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### vaesef.vv v1,v2 (crypto_aes_round_last [1,2]) — final-round encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020a2")
```

</details>

#### vaesef.vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### vaesdm.vv v1,v2 (crypto_aes_inv_round [1,2]) — mid-round decrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020ae")
```

</details>

#### vaesdm.vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

#### vaesdf.vv v1,v2 (crypto_aes_inv_round_last [1,2]) — final-round decrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.lowered).to_equal(true)
expect(result.reason).to_equal("")
expect(_list_hex(result.bytes)).to_equal("d72020aa")
```

</details>

#### vaesdf.vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("crypto_aes_inv_round_last", [1, 2], TEST_RV64_CAPS)
expect(result.bytes.len()).to_equal(4)
```

</details>

### RV64 Zvk cipher intrinsic lowering — failure cases

#### unknown intrinsic returns lowered=false, reason=unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lower_cipher_intrinsic_riscv("unknown_intrinsic", [0, 0], TEST_RV64_CAPS)
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
val result = lower_cipher_intrinsic_riscv("crypto_aes_round", [0], TEST_RV64_CAPS)
expect(result.lowered).to_equal(false)
expect(result.reason).to_equal("bad-arity")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/lowering_riscv_crypto_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV64 Zvk cipher intrinsic lowering — AES rounds
- RV64 Zvk cipher intrinsic lowering — failure cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
