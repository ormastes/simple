# Encode X86 64 Crypto Specification

> <details>

<!-- sdn-diagram:id=encode_x86_64_crypto_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_x86_64_crypto_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_x86_64_crypto_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_x86_64_crypto_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode X86 64 Crypto Specification

## Scenarios

### x86 AES-NI encoder — golden bytes

#### emit_aesenc(0,0) → [0x66, 0x0F, 0x38, 0xDC, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_aesenc(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDC)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesenc(8,0) → [0x66, 0x44, 0x0F, 0x38, 0xDC, 0xC0] (REX.R for dst>=8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_aesenc(8, 0)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x44)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x38)
expect(bytes[4]).to_equal(0xDC)
expect(bytes[5]).to_equal(0xC0)
```

</details>

#### emit_aesenclast(0,0) → [0x66, 0x0F, 0x38, 0xDD, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_aesenclast(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDD)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesdec(0,0) → [0x66, 0x0F, 0x38, 0xDE, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_aesdec(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDE)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesdeclast(0,0) → [0x66, 0x0F, 0x38, 0xDF, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_aesdeclast(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDF)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aesimc(0,0) → [0x66, 0x0F, 0x38, 0xDB, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_aesimc(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xDB)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_aeskeygenassist(0,0,0x10) → [0x66, 0x0F, 0x3A, 0xDF, 0xC0, 0x10]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_aeskeygenassist(0, 0, 0x10)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0xDF)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x10)
```

</details>

### x86 SHA-NI encoder — golden bytes

#### emit_sha256rnds2(0,0) → [0x0F, 0x38, 0xCB, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_sha256rnds2(0, 0)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x0F)
expect(bytes[1]).to_equal(0x38)
expect(bytes[2]).to_equal(0xCB)
expect(bytes[3]).to_equal(0xC0)
```

</details>

#### emit_sha256msg1(0,0) → [0x0F, 0x38, 0xCC, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_sha256msg1(0, 0)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x0F)
expect(bytes[1]).to_equal(0x38)
expect(bytes[2]).to_equal(0xCC)
expect(bytes[3]).to_equal(0xC0)
```

</details>

#### emit_sha256msg2(0,0) → [0x0F, 0x38, 0xCD, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_sha256msg2(0, 0)
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x0F)
expect(bytes[1]).to_equal(0x38)
expect(bytes[2]).to_equal(0xCD)
expect(bytes[3]).to_equal(0xC0)
```

</details>

### x86 CRC32 encoder — golden bytes

#### emit_crc32_r32_r32(0,0) → [0xF2, 0x0F, 0x38, 0xF1, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_crc32_r32_r32(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0xF2)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0xF1)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_crc32_r64_r64(0,0) → [0xF2, 0x48, 0x0F, 0x38, 0xF1, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_crc32_r64_r64(0, 0)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0xF2)
expect(bytes[1]).to_equal(0x48)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x38)
expect(bytes[4]).to_equal(0xF1)
expect(bytes[5]).to_equal(0xC0)
```

</details>

### x86 PCLMULQDQ encoder

#### emit_pclmulqdq(0,0,0x00) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pclmulqdq(0, 0, 0x00)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x44)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x00)
```

</details>

#### emit_pclmulqdq(0,0,0x11) → [0x66, 0x0F, 0x3A, 0x44, 0xC0, 0x11]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pclmulqdq(0, 0, 0x11)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x44)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/encode_x86_64_crypto_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86 AES-NI encoder — golden bytes
- x86 SHA-NI encoder — golden bytes
- x86 CRC32 encoder — golden bytes
- x86 PCLMULQDQ encoder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
