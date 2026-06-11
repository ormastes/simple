# X86 Sse41 Specification

> <details>

<!-- sdn-diagram:id=x86_sse41_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_sse41_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_sse41_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_sse41_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Sse41 Specification

## Scenarios

### x86 SSE4.1 PBLENDW encoder — golden bytes

#### emit_pblendw(0, 1, 0xFF) → [0x66, 0x0F, 0x3A, 0x0E, 0xC1, 0xFF]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pblendw(0, 1, 0xFF)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x0E)
expect(bytes[4]).to_equal(0xC1)
expect(bytes[5]).to_equal(0xFF)
```

</details>

#### emit_pblendw(0, 0, 0x00) → [0x66, 0x0F, 0x3A, 0x0E, 0xC0, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pblendw(0, 0, 0x00)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x0E)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x00)
```

</details>

#### emit_pblendw(8, 9, 0x0A) → [0x66, 0x45, 0x0F, 0x3A, 0x0E, 0xC1, 0x0A] (REX.RB)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pblendw(8, 9, 0x0A)
expect(bytes.len()).to_equal(7)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x45)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x3A)
expect(bytes[4]).to_equal(0x0E)
expect(bytes[5]).to_equal(0xC1)
expect(bytes[6]).to_equal(0x0A)
```

</details>

### x86 SSE4.1 BLENDPS encoder — golden bytes

#### emit_blendps(0, 1, 0x0F) → [0x66, 0x0F, 0x3A, 0x0C, 0xC1, 0x0F]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_blendps(0, 1, 0x0F)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x0C)
expect(bytes[4]).to_equal(0xC1)
expect(bytes[5]).to_equal(0x0F)
```

</details>

#### emit_blendps(0, 0, 0x00) → [0x66, 0x0F, 0x3A, 0x0C, 0xC0, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_blendps(0, 0, 0x00)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x0C)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x00)
```

</details>

#### emit_blendps(8, 0, 0x05) → [0x66, 0x44, 0x0F, 0x3A, 0x0C, 0xC0, 0x05] (REX.R only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_blendps(8, 0, 0x05)
expect(bytes.len()).to_equal(7)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x44)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x3A)
expect(bytes[4]).to_equal(0x0C)
expect(bytes[5]).to_equal(0xC0)
expect(bytes[6]).to_equal(0x05)
```

</details>

### x86 SSE4.1 BLENDPD encoder — golden bytes

#### emit_blendpd(0, 1, 0x03) → [0x66, 0x0F, 0x3A, 0x0D, 0xC1, 0x03]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_blendpd(0, 1, 0x03)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x0D)
expect(bytes[4]).to_equal(0xC1)
expect(bytes[5]).to_equal(0x03)
```

</details>

#### emit_blendpd(0, 0, 0x00) → [0x66, 0x0F, 0x3A, 0x0D, 0xC0, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_blendpd(0, 0, 0x00)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x0D)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x00)
```

</details>

#### emit_blendpd(0, 8, 0x01) → [0x66, 0x41, 0x0F, 0x3A, 0x0D, 0xC0, 0x01] (REX.B only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_blendpd(0, 8, 0x01)
expect(bytes.len()).to_equal(7)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x41)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x3A)
expect(bytes[4]).to_equal(0x0D)
expect(bytes[5]).to_equal(0xC0)
expect(bytes[6]).to_equal(0x01)
```

</details>

### x86 SSE4.1 PBLENDVB encoder — golden bytes

#### emit_pblendvb(0, 1) → [0x66, 0x0F, 0x38, 0x10, 0xC1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pblendvb(0, 1)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0x10)
expect(bytes[4]).to_equal(0xC1)
```

</details>

#### emit_pblendvb(0, 0) → [0x66, 0x0F, 0x38, 0x10, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pblendvb(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0x10)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_pblendvb(8, 0) → [0x66, 0x44, 0x0F, 0x38, 0x10, 0xC0] (REX.R)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pblendvb(8, 0)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x44)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x38)
expect(bytes[4]).to_equal(0x10)
expect(bytes[5]).to_equal(0xC0)
```

</details>

### x86 SSE4.1 PACKUSDW encoder — golden bytes

#### emit_packusdw(0, 1) → [0x66, 0x0F, 0x38, 0x2B, 0xC1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_packusdw(0, 1)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0x2B)
expect(bytes[4]).to_equal(0xC1)
```

</details>

#### emit_packusdw(0, 0) → [0x66, 0x0F, 0x38, 0x2B, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_packusdw(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0x2B)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_packusdw(8, 0) → [0x66, 0x44, 0x0F, 0x38, 0x2B, 0xC0] (REX.R)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_packusdw(8, 0)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x44)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x38)
expect(bytes[4]).to_equal(0x2B)
expect(bytes[5]).to_equal(0xC0)
```

</details>

### x86 SSE4.1 PMOVZXBD encoder — golden bytes

#### emit_pmovzxbd(0, 1) → [0x66, 0x0F, 0x38, 0x31, 0xC1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pmovzxbd(0, 1)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0x31)
expect(bytes[4]).to_equal(0xC1)
```

</details>

#### emit_pmovzxbd(0, 0) → [0x66, 0x0F, 0x38, 0x31, 0xC0]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pmovzxbd(0, 0)
expect(bytes.len()).to_equal(5)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x38)
expect(bytes[3]).to_equal(0x31)
expect(bytes[4]).to_equal(0xC0)
```

</details>

#### emit_pmovzxbd(0, 9) → [0x66, 0x41, 0x0F, 0x38, 0x31, 0xC1] (REX.B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_pmovzxbd(0, 9)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x41)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x38)
expect(bytes[4]).to_equal(0x31)
expect(bytes[5]).to_equal(0xC1)
```

</details>

### x86 SSE4.1 DPPS encoder — golden bytes

#### emit_dpps(0, 1, 0xFF) → [0x66, 0x0F, 0x3A, 0x40, 0xC1, 0xFF]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_dpps(0, 1, 0xFF)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x40)
expect(bytes[4]).to_equal(0xC1)
expect(bytes[5]).to_equal(0xFF)
```

</details>

#### emit_dpps(0, 0, 0x00) → [0x66, 0x0F, 0x3A, 0x40, 0xC0, 0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_dpps(0, 0, 0x00)
expect(bytes.len()).to_equal(6)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x0F)
expect(bytes[2]).to_equal(0x3A)
expect(bytes[3]).to_equal(0x40)
expect(bytes[4]).to_equal(0xC0)
expect(bytes[5]).to_equal(0x00)
```

</details>

#### emit_dpps(8, 9, 0xF1) → [0x66, 0x45, 0x0F, 0x3A, 0x40, 0xC1, 0xF1] (REX.RB)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_dpps(8, 9, 0xF1)
expect(bytes.len()).to_equal(7)
expect(bytes[0]).to_equal(0x66)
expect(bytes[1]).to_equal(0x45)
expect(bytes[2]).to_equal(0x0F)
expect(bytes[3]).to_equal(0x3A)
expect(bytes[4]).to_equal(0x40)
expect(bytes[5]).to_equal(0xC1)
expect(bytes[6]).to_equal(0xF1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/x86_sse41_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86 SSE4.1 PBLENDW encoder — golden bytes
- x86 SSE4.1 BLENDPS encoder — golden bytes
- x86 SSE4.1 BLENDPD encoder — golden bytes
- x86 SSE4.1 PBLENDVB encoder — golden bytes
- x86 SSE4.1 PACKUSDW encoder — golden bytes
- x86 SSE4.1 PMOVZXBD encoder — golden bytes
- x86 SSE4.1 DPPS encoder — golden bytes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
