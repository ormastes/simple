# Encode Aarch64 Crypto Specification

> 1. var b = emit aese

<!-- sdn-diagram:id=encode_aarch64_crypto_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_aarch64_crypto_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_aarch64_crypto_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_aarch64_crypto_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode Aarch64 Crypto Specification

## Scenarios

### emit_aese — AES single-round encryption

#### AESE V1, V2 encodes to correct LE bytes

1. var b = emit aese
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_aese(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

#### AESE V0, V0 produces base opcode bytes

1. var b = emit aese
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_aese(0, 0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_aesd — AES single-round decryption

#### AESD V1, V2 encodes to correct LE bytes

1. var b = emit aesd
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x58`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_aesd(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x58)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_aesmc_aarch64 — AES mix columns

#### AESMC V1, V1 encodes to correct LE bytes

1. var b = emit aesmc aarch64
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x21`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_aesmc_aarch64(1, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x21)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_aesimc_aarch64 — AES inverse mix columns

#### AESIMC V1, V2 encodes to correct LE bytes

1. var b = emit aesimc aarch64
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_aesimc_aarch64(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_sha256h — SHA-256 hash update part 1

#### SHA256H Q0, Q1, V2 encodes to correct LE bytes

1. var b = emit sha256h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0x02`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_sha256h(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0x02)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_sha256h2 — SHA-256 hash update part 2

#### SHA256H2 Q0, Q1, V2 encodes to correct LE bytes

1. var b = emit sha256h2
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x50`
   - Expected: b[2] equals `0x02`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_sha256h2(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x50)
expect(b[2]).to_equal(0x02)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_sha256su0 — SHA-256 schedule update 0

#### SHA256SU0 V1, V2 encodes to correct LE bytes

1. var b = emit sha256su0
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x28`
   - Expected: b[2] equals `0x28`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_sha256su0(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x28)
expect(b[2]).to_equal(0x28)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_sha256su1 — SHA-256 schedule update 1

#### SHA256SU1 V0, V1, V2 encodes to correct LE bytes

1. var b = emit sha256su1
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x60`
   - Expected: b[2] equals `0x02`
   - Expected: b[3] equals `0x5E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_sha256su1(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x60)
expect(b[2]).to_equal(0x02)
expect(b[3]).to_equal(0x5E)
```

</details>

### emit_pmull — polynomial multiply lower halves

#### PMULL V0, V1, V2 encodes to correct LE bytes

1. var b = emit pmull
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xE0`
   - Expected: b[2] equals `0xE2`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_pmull(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0xE2)
expect(b[3]).to_equal(0x0E)
```

</details>

### emit_pmull2 — polynomial multiply upper halves

#### PMULL2 V0, V1, V2 encodes to correct LE bytes

1. var b = emit pmull2
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xE0`
   - Expected: b[2] equals `0xE2`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_pmull2(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0xE2)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_crc32b — CRC32 byte accumulate

#### CRC32B W0, W1, W2 encodes to correct LE bytes

1. var b = emit crc32b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_crc32b(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_crc32h — CRC32 halfword accumulate

#### CRC32H W0, W1, W2 encodes to correct LE bytes

1. var b = emit crc32h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x44`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_crc32h(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_crc32w — CRC32 word accumulate

#### CRC32W W0, W1, W2 encodes to correct LE bytes

1. var b = emit crc32w
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_crc32w(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_crc32x — CRC32 doubleword accumulate

#### CRC32X W0, W1, X2 encodes to correct LE bytes

1. var b = emit crc32x
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x4C`
   - Expected: b[2] equals `0xC2`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_crc32x(0, 1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x4C)
expect(b[2]).to_equal(0xC2)
expect(b[3]).to_equal(0x9A)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/encode_aarch64_crypto_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_aese — AES single-round encryption
- emit_aesd — AES single-round decryption
- emit_aesmc_aarch64 — AES mix columns
- emit_aesimc_aarch64 — AES inverse mix columns
- emit_sha256h — SHA-256 hash update part 1
- emit_sha256h2 — SHA-256 hash update part 2
- emit_sha256su0 — SHA-256 schedule update 0
- emit_sha256su1 — SHA-256 schedule update 1
- emit_pmull — polynomial multiply lower halves
- emit_pmull2 — polynomial multiply upper halves
- emit_crc32b — CRC32 byte accumulate
- emit_crc32h — CRC32 halfword accumulate
- emit_crc32w — CRC32 word accumulate
- emit_crc32x — CRC32 doubleword accumulate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
