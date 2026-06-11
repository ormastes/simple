# X86 Bmi2 Specification

> 1. expect result len

<!-- sdn-diagram:id=x86_bmi2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_bmi2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_bmi2_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_bmi2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Bmi2 Specification

## Scenarios

### BMI2 emit_pdep_r64 rax rcx rdx golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r64(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r64(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dst<8 → ~R=1, rm(src2)<8 → ~B=1, ~X=1, mmmmm=2 → 226
val result = emit_pdep_r64(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=1, ~vvvv=(15-src1=1)=14, L=0, pp=3(F2) → 128+14*8+3=243
val result = emit_pdep_r64(0, 1, 2)
expect result[2] == 243
```

</details>

#### byte3 is opcode 0xF5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r64(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=dst%8=0, rm=src2%8=2 → 192+0*8+2=194
val result = emit_pdep_r64(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pdep_r64 extended dst r9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dst>=8 → ~R=0; rm(src2)<8 → ~B=1 → 226-128=98
val result = emit_pdep_r64(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r64(9, 1, 2)
expect result[2] == 243
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=9%8=1, rm=2%8=2 → 192+1*8+2=202
val result = emit_pdep_r64(9, 1, 2)
expect result[4] == 202
```

</details>

### BMI2 emit_pdep_r64 extended src1 r9

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r64(0, 9, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xB3 (W=1 ~vvvv=6 L=0 pp=3/F2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=1, ~vvvv=(15-src1=9)=6, L=0, pp=3(F2) → 128+6*8+3=179
val result = emit_pdep_r64(0, 9, 2)
expect result[2] == 179
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r64(0, 9, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pdep_r64 extended src2 r9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dst<8 → ~R=1; rm(src2=9)>=8 → ~B=0 → 226-32=194
val result = emit_pdep_r64(0, 1, 9)
expect result[1] == 194
```

</details>

#### byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r64(0, 1, 9)
expect result[2] == 243
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=0%8=0, rm=9%8=1 → 192+0*8+1=193
val result = emit_pdep_r64(0, 1, 9)
expect result[4] == 193
```

</details>

### BMI2 emit_pdep_r32 eax ecx edx golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=0, ~vvvv=14, L=0, pp=3 → 14*8+3=115
val result = emit_pdep_r32(0, 1, 2)
expect result[2] == 115
```

</details>

#### byte3 is opcode 0xF5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pdep_r32 extended src2 r9d

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 9)
expect result[1] == 194
```

</details>

#### byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 9)
expect result[2] == 115
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pdep_r32(0, 1, 9)
expect result[4] == 193
```

</details>

### BMI2 emit_pext_r64 rax rcx rdx golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=1, ~vvvv=14, L=0, pp=2(F3) → 128+14*8+2=242
val result = emit_pext_r64(0, 1, 2)
expect result[2] == 242
```

</details>

#### byte3 is opcode 0xF5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pext_r64 extended dst r9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(9, 1, 2)
expect result[2] == 242
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r64(9, 1, 2)
expect result[4] == 202
```

</details>

### BMI2 emit_pext_r32 eax ecx edx golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r32(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte1 is 0xE2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r32(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x72 (W=0 ~vvvv=14 L=0 pp=2/F3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=0, ~vvvv=14, L=0, pp=2(F3) → 14*8+2=114
val result = emit_pext_r32(0, 1, 2)
expect result[2] == 114
```

</details>

#### byte3 is opcode 0xF5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r32(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_pext_r32(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_bzhi_r64 rax rcx rdx golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r64(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r64(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dst<8 → ~R=1; rm(src=1)<8 → ~B=1 → 226
val result = emit_bzhi_r64(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=1, ~vvvv=(15-idx=2)=13, L=0, pp=0(NP) → 128+13*8+0=232
val result = emit_bzhi_r64(0, 1, 2)
expect result[2] == 232
```

</details>

#### byte3 is opcode 0xF5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r64(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=dst%8=0, rm=src%8=1 → 192+0*8+1=193
val result = emit_bzhi_r64(0, 1, 2)
expect result[4] == 193
```

</details>

### BMI2 emit_bzhi_r64 extended dst r9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dst>=8 → ~R=0; rm(src=1)<8 → ~B=1 → 226-128=98
val result = emit_bzhi_r64(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r64(9, 1, 2)
expect result[2] == 232
```

</details>

#### byte4 is ModRM 0xC9 (mod=11 reg=1 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=9%8=1, rm=1%8=1 → 192+1*8+1=201
val result = emit_bzhi_r64(9, 1, 2)
expect result[4] == 201
```

</details>

### BMI2 emit_bzhi_r64 extended idx r9

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rm(src=1)<8 → ~B=1 → 226
val result = emit_bzhi_r64(0, 1, 9)
expect result[1] == 226
```

</details>

#### byte2 is 0xB0 (W=1 ~vvvv=6 L=0 pp=0/NP)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=1, ~vvvv=(15-idx=9)=6, L=0, pp=0(NP) → 128+6*8+0=176
val result = emit_bzhi_r64(0, 1, 9)
expect result[2] == 176
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r64(0, 1, 9)
expect result[4] == 193
```

</details>

### BMI2 emit_bzhi_r64 extended src r9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# dst<8 → ~R=1; rm(src=9)>=8 → ~B=0 → 226-32=194
val result = emit_bzhi_r64(0, 9, 2)
expect result[1] == 194
```

</details>

#### byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r64(0, 9, 2)
expect result[2] == 232
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=11, reg=0%8=0, rm=9%8=1 → 192+0*8+1=193
val result = emit_bzhi_r64(0, 9, 2)
expect result[4] == 193
```

</details>

### BMI2 emit_bzhi_r32 eax ecx edx golden

#### emits 5 bytes

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r32(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte1 is 0xE2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r32(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x68 (W=0 ~vvvv=13 L=0 pp=0/NP)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=0, ~vvvv=(15-idx=2)=13, L=0, pp=0(NP) → 13*8+0=104
val result = emit_bzhi_r32(0, 1, 2)
expect result[2] == 104
```

</details>

#### byte3 is opcode 0xF5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r32(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_bzhi_r32(0, 1, 2)
expect result[4] == 193
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/x86_bmi2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BMI2 emit_pdep_r64 rax rcx rdx golden
- BMI2 emit_pdep_r64 extended dst r9
- BMI2 emit_pdep_r64 extended src1 r9
- BMI2 emit_pdep_r64 extended src2 r9
- BMI2 emit_pdep_r32 eax ecx edx golden
- BMI2 emit_pdep_r32 extended src2 r9d
- BMI2 emit_pext_r64 rax rcx rdx golden
- BMI2 emit_pext_r64 extended dst r9
- BMI2 emit_pext_r32 eax ecx edx golden
- BMI2 emit_bzhi_r64 rax rcx rdx golden
- BMI2 emit_bzhi_r64 extended dst r9
- BMI2 emit_bzhi_r64 extended idx r9
- BMI2 emit_bzhi_r64 extended src r9
- BMI2 emit_bzhi_r32 eax ecx edx golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
