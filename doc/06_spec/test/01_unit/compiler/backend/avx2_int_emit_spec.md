# Avx2 Int Emit Specification

> 1. expect result len

<!-- sdn-diagram:id=avx2_int_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx2_int_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx2_int_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx2_int_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 68 | 68 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx2 Int Emit Specification

## Scenarios

### AVX2 emit_vpaddd_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX 3-byte escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 2)
expect result[1] == 225
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

#### byte3 is opcode 0xFE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 2)
expect result[3] == 254
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpaddd_ymm extended dst ymm8

#### byte1 is 0x61 (~R=0 ~X=1 ~B=1 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(8, 1, 2)
expect result[1] == 97
```

</details>

#### byte2 unchanged at 0x75

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(8, 1, 2)
expect result[2] == 117
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# reg=8%8=0, rm=2%8=2 → 194
val result = emit_vpaddd_ymm(8, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpaddd_ymm extended rn ymm9

#### byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 9, 2)
expect result[2] == 53
```

</details>

### AVX2 emit_vpaddd_ymm extended rm ymm8

#### byte1 is 0xC1 (~R=1 ~X=1 ~B=0 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 8)
expect result[1] == 193
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpaddd_ymm(0, 1, 8)
expect result[4] == 192
```

</details>

### AVX2 emit_vpsubd_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(0, 1, 2)
expect result[1] == 225
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

#### byte3 is opcode 0xFA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(0, 1, 2)
expect result[3] == 250
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpsubd_ymm ymm3 ymm4 ymm5

#### byte2 is 0x5D (W=0 ~vvvv=11 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(3, 4, 5)
expect result[2] == 93
```

</details>

#### byte4 is ModRM 0xDD (mod=11 reg=3 rm=5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsubd_ymm(3, 4, 5)
expect result[4] == 221
```

</details>

### AVX2 emit_vpmulld_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (0F38 map mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

#### byte3 is opcode 0x40

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 1, 2)
expect result[3] == 64
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpmulld_ymm ymm0 ymm3 ymm4

#### byte2 is 0x65 (W=0 ~vvvv=12 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 3, 4)
expect result[2] == 101
```

</details>

#### byte4 is ModRM 0xC4 (mod=11 reg=0 rm=4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpmulld_ymm(0, 3, 4)
expect result[4] == 196
```

</details>

### AVX2 emit_vpand_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpand_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xDB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpand_ymm(0, 1, 2)
expect result[3] == 219
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpand_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpand_ymm ymm0 ymm2 ymm3

#### byte2 is 0x6D (W=0 ~vvvv=13 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpand_ymm(0, 2, 3)
expect result[2] == 109
```

</details>

#### byte4 is ModRM 0xC3 (mod=11 reg=0 rm=3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpand_ymm(0, 2, 3)
expect result[4] == 195
```

</details>

### AVX2 emit_vpor_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpor_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xEB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpor_ymm(0, 1, 2)
expect result[3] == 235
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpor_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpor_ymm ymm0 ymm3 ymm4

#### byte2 is 0x65

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpor_ymm(0, 3, 4)
expect result[2] == 101
```

</details>

#### byte4 is ModRM 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpor_ymm(0, 3, 4)
expect result[4] == 196
```

</details>

### AVX2 emit_vpxor_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpxor_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xEF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpxor_ymm(0, 1, 2)
expect result[3] == 239
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpxor_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpxor_ymm ymm0 ymm4 ymm5

#### byte2 is 0x5D (W=0 ~vvvv=11 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpxor_ymm(0, 4, 5)
expect result[2] == 93
```

</details>

#### byte4 is ModRM 0xC5 (mod=11 reg=0 rm=5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpxor_ymm(0, 4, 5)
expect result[4] == 197
```

</details>

### AVX2 emit_vpsrld_ymm_imm ymm0 ymm1 imm8=8 golden

#### emits 6 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 1, 8)
expect result.len() == 6
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 1, 8)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 1, 8)
expect result[1] == 225
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rd=0 → vvvv=0 → ~vvvv=15 → 15*8+5=125
val result = emit_vpsrld_ymm_imm(0, 1, 8)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x72

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 1, 8)
expect result[3] == 114
```

</details>

#### byte4 is ModRM 0xD1 (mod=11 reg=2 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 1, 8)
expect result[4] == 209
```

</details>

#### byte5 is imm8 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 1, 8)
expect result[5] == 8
```

</details>

### AVX2 emit_vpsrld_ymm_imm ymm1 ymm2 imm8=16

#### byte2 is 0x75 (vvvv=rd=1 → ~vvvv=14)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(1, 2, 16)
expect result[2] == 117
```

</details>

#### byte4 is ModRM 0xD2 (mod=11 reg=2 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(1, 2, 16)
expect result[4] == 210
```

</details>

#### byte5 is imm8 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(1, 2, 16)
expect result[5] == 16
```

</details>

### AVX2 emit_vpsrld_ymm_imm extended rn ymm8

#### byte1 is 0xC1 (~R=1 ~X=1 ~B=0 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 8, 4)
expect result[1] == 193
```

</details>

#### byte4 is ModRM 0xD0 (mod=11 reg=2 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpsrld_ymm_imm(0, 8, 4)
expect result[4] == 208
```

</details>

### AVX2 emit_vpslld_ymm_imm ymm0 ymm1 imm8=3 golden

#### emits 6 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 1, 3)
expect result.len() == 6
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 1, 3)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 1, 3)
expect result[1] == 225
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 1, 3)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x72

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 1, 3)
expect result[3] == 114
```

</details>

#### byte4 is ModRM 0xF1 (mod=11 reg=6 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 1, 3)
expect result[4] == 241
```

</details>

#### byte5 is imm8 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 1, 3)
expect result[5] == 3
```

</details>

### AVX2 emit_vpslld_ymm_imm ymm2 ymm3 imm8=5

#### byte2 is 0x6D (vvvv=rd=2 → ~vvvv=13)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(2, 3, 5)
expect result[2] == 109
```

</details>

#### byte4 is ModRM 0xF3 (mod=11 reg=6 rm=3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(2, 3, 5)
expect result[4] == 243
```

</details>

#### byte5 is imm8 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(2, 3, 5)
expect result[5] == 5
```

</details>

### AVX2 emit_vpslld_ymm_imm extended rn ymm8

#### byte1 is 0xC1 (~R=1 ~X=1 ~B=0 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 8, 4)
expect result[1] == 193
```

</details>

#### byte4 is ModRM 0xF0 (mod=11 reg=6 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 8, 4)
expect result[4] == 240
```

</details>

#### byte5 is imm8 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpslld_ymm_imm(0, 8, 4)
expect result[5] == 4
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx2_int_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX2 emit_vpaddd_ymm ymm0 ymm1 ymm2 golden
- AVX2 emit_vpaddd_ymm extended dst ymm8
- AVX2 emit_vpaddd_ymm extended rn ymm9
- AVX2 emit_vpaddd_ymm extended rm ymm8
- AVX2 emit_vpsubd_ymm ymm0 ymm1 ymm2 golden
- AVX2 emit_vpsubd_ymm ymm3 ymm4 ymm5
- AVX2 emit_vpmulld_ymm ymm0 ymm1 ymm2 golden
- AVX2 emit_vpmulld_ymm ymm0 ymm3 ymm4
- AVX2 emit_vpand_ymm ymm0 ymm1 ymm2 golden
- AVX2 emit_vpand_ymm ymm0 ymm2 ymm3
- AVX2 emit_vpor_ymm ymm0 ymm1 ymm2 golden
- AVX2 emit_vpor_ymm ymm0 ymm3 ymm4
- AVX2 emit_vpxor_ymm ymm0 ymm1 ymm2 golden
- AVX2 emit_vpxor_ymm ymm0 ymm4 ymm5
- AVX2 emit_vpsrld_ymm_imm ymm0 ymm1 imm8=8 golden
- AVX2 emit_vpsrld_ymm_imm ymm1 ymm2 imm8=16
- AVX2 emit_vpsrld_ymm_imm extended rn ymm8
- AVX2 emit_vpslld_ymm_imm ymm0 ymm1 imm8=3 golden
- AVX2 emit_vpslld_ymm_imm ymm2 ymm3 imm8=5
- AVX2 emit_vpslld_ymm_imm extended rn ymm8

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 68 |
| Active scenarios | 68 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
