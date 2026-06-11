# Avx2 Cmp Emit Specification

> 1. expect result len

<!-- sdn-diagram:id=avx2_cmp_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx2_cmp_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx2_cmp_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx2_cmp_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx2 Cmp Emit Specification

## Scenarios

### AVX2 emit_vpcmpeqd_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte0 is VEX 3-byte escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x76

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[3] == 118
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpcmpeqd_ymm ymm3 ymm5 ymm7

#### byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(3, 5, 7)
expect result[2] == 85
```

</details>

#### byte4 is ModRM 0xDF (mod=11 reg=3 rm=7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqd_ymm(3, 5, 7)
expect result[4] == 223
```

</details>

### AVX2 emit_vpcmpgtd_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[1] == 225
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

#### byte3 is opcode 0x66

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[3] == 102
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpcmpgtd_ymm ymm2 ymm4 ymm6

#### byte2 is 0x5D (W=0 ~vvvv=11 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(2, 4, 6)
expect result[2] == 93
```

</details>

#### byte4 is ModRM 0xD6 (mod=11 reg=2 rm=6)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtd_ymm(2, 4, 6)
expect result[4] == 214
```

</details>

### AVX2 emit_vpcmpeqb_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x74

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[3] == 116
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpcmpeqb_ymm ymm1 ymm2 ymm3

#### byte2 is 0x6D (W=0 ~vvvv=13 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(1, 2, 3)
expect result[2] == 109
```

</details>

#### byte4 is ModRM 0xCB (mod=11 reg=1 rm=3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpeqb_ymm(1, 2, 3)
expect result[4] == 203
```

</details>

### AVX2 emit_vpcmpgtb_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtb_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtb_ymm(0, 0, 0)
expect result[3] == 100
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtb_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpcmpgtb_ymm ymm4 ymm3 ymm2

#### byte2 is 0x65 (W=0 ~vvvv=12 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtb_ymm(4, 3, 2)
expect result[2] == 101
```

</details>

#### byte4 is ModRM 0xE2 (mod=11 reg=4 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpcmpgtb_ymm(4, 3, 2)
expect result[4] == 226
```

</details>

### AVX2 emit_vpermd_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (0F38 map mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(0, 0, 0)
expect result[1] == 226
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x36

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(0, 0, 0)
expect result[3] == 54
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpermd_ymm ymm3 ymm5 ymm7

#### byte1 is 0xE2 (0F38 map)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(3, 5, 7)
expect result[1] == 226
```

</details>

#### byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(3, 5, 7)
expect result[2] == 85
```

</details>

#### byte4 is ModRM 0xDF (mod=11 reg=3 rm=7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpermd_ymm(3, 5, 7)
expect result[4] == 223
```

</details>

### AVX2 emit_vpshufb_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (0F38 map mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[1] == 226
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[3] == 0
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpshufb_ymm ymm2 ymm1 ymm3

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(2, 1, 3)
expect result[2] == 117
```

</details>

#### byte4 is ModRM 0xD3 (mod=11 reg=2 rm=3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufb_ymm(2, 1, 3)
expect result[4] == 211
```

</details>

### AVX2 emit_vpshufd_ymm ymm0 ymm0 imm=0 golden

#### emits 6 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(0, 0, 0)
expect result.len() == 6
```

</details>

#### byte0 is VEX 3-byte escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x05 (vvvv=1111 W=0 L=1 pp=01)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vvvv=15 → ~vvvv=0 → 0*8+5=5
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[2] == 5
```

</details>

#### byte3 is opcode 0x70

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[3] == 112
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

#### byte5 is imm8 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[5] == 0
```

</details>

### AVX2 emit_vpshufd_ymm ymm3 ymm5 imm=0xAA

#### byte2 is 0x05 (vvvv=1111 always)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(3, 5, 170)
expect result[2] == 5
```

</details>

#### byte4 is ModRM 0xDD (mod=11 reg=3 rm=5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(3, 5, 170)
expect result[4] == 221
```

</details>

#### byte5 is imm8 0xAA

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_vpshufd_ymm(3, 5, 170)
expect result[5] == 170
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx2_cmp_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX2 emit_vpcmpeqd_ymm ymm0 ymm0 ymm0 golden
- AVX2 emit_vpcmpeqd_ymm ymm3 ymm5 ymm7
- AVX2 emit_vpcmpgtd_ymm ymm0 ymm1 ymm2 golden
- AVX2 emit_vpcmpgtd_ymm ymm2 ymm4 ymm6
- AVX2 emit_vpcmpeqb_ymm ymm0 ymm0 ymm0 golden
- AVX2 emit_vpcmpeqb_ymm ymm1 ymm2 ymm3
- AVX2 emit_vpcmpgtb_ymm ymm0 ymm0 ymm0 golden
- AVX2 emit_vpcmpgtb_ymm ymm4 ymm3 ymm2
- AVX2 emit_vpermd_ymm ymm0 ymm0 ymm0 golden
- AVX2 emit_vpermd_ymm ymm3 ymm5 ymm7
- AVX2 emit_vpshufb_ymm ymm0 ymm0 ymm0 golden
- AVX2 emit_vpshufb_ymm ymm2 ymm1 ymm3
- AVX2 emit_vpshufd_ymm ymm0 ymm0 imm=0 golden
- AVX2 emit_vpshufd_ymm ymm3 ymm5 imm=0xAA

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
