# X86 Bmi2 Specification

> Tests covering BMI2 emit_pdep_r64 rax rcx rdx golden, BMI2 emit_pdep_r64 extended dst r9, BMI2 emit_pdep_r64 extended src1 r9, BMI2 emit_pdep_r64 extended src2 r9, BMI2 emit_pdep_r32 eax ecx edx golden, BMI2 emit_pdep_r32 extended src2 r9d, BMI2 emit_pext_r64 rax rcx rdx golden, BMI2 emit_pext_r64 extended dst r9, BMI2 emit_pext_r32 eax ecx edx golden, BMI2 emit_bzhi_r64 rax rcx rdx golden, BMI2 emit_bzhi_r64 extended dst r9, BMI2 emit_bzhi_r64 extended idx r9, BMI2 emit_bzhi_r64 extended src r9, BMI2 emit_bzhi_r32 eax ecx edx golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 Bmi2 Specification

## Scenarios

### BMI2 emit_pdep_r64 rax rcx rdx golden

#### emits 5 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_pdep_r64(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

- byte0 is VEX escape 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is VEX escape 0xC4")
val result = emit_pdep_r64(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)")
# dst<8 → ~R=1, rm(src2)<8 → ~B=1, ~X=1, mmmmm=2 → 226
val result = emit_pdep_r64(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)

- byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)")
# W=1, ~vvvv=(15-src1=1)=14, L=0, pp=3(F2) → 128+14*8+3=243
val result = emit_pdep_r64(0, 1, 2)
expect result[2] == 243
```

</details>

#### byte3 is opcode 0xF5

- byte3 is opcode 0xF5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xF5")
val result = emit_pdep_r64(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

- byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)")
# mod=11, reg=dst%8=0, rm=src2%8=2 → 192+0*8+2=194
val result = emit_pdep_r64(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pdep_r64 extended dst r9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)")
# dst>=8 → ~R=0; rm(src2)<8 → ~B=1 → 226-128=98
val result = emit_pdep_r64(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)

- byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)")
val result = emit_pdep_r64(9, 1, 2)
expect result[2] == 243
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

- byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)")
# mod=11, reg=9%8=1, rm=2%8=2 → 192+1*8+2=202
val result = emit_pdep_r64(9, 1, 2)
expect result[4] == 202
```

</details>

### BMI2 emit_pdep_r64 extended src1 r9

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)")
val result = emit_pdep_r64(0, 9, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xB3 (W=1 ~vvvv=6 L=0 pp=3/F2)

- byte2 is 0xB3 (W=1 ~vvvv=6 L=0 pp=3/F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xB3 (W=1 ~vvvv=6 L=0 pp=3/F2)")
# W=1, ~vvvv=(15-src1=9)=6, L=0, pp=3(F2) → 128+6*8+3=179
val result = emit_pdep_r64(0, 9, 2)
expect result[2] == 179
```

</details>

#### byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)

- byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC2 (mod=11 reg=0 rm=2)")
val result = emit_pdep_r64(0, 9, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pdep_r64 extended src2 r9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

- byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)")
# dst<8 → ~R=1; rm(src2=9)>=8 → ~B=0 → 226-32=194
val result = emit_pdep_r64(0, 1, 9)
expect result[1] == 194
```

</details>

#### byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)

- byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xF3 (W=1 ~vvvv=14 L=0 pp=3/F2)")
val result = emit_pdep_r64(0, 1, 9)
expect result[2] == 243
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

- byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)")
# mod=11, reg=0%8=0, rm=9%8=1 → 192+0*8+1=193
val result = emit_pdep_r64(0, 1, 9)
expect result[4] == 193
```

</details>

### BMI2 emit_pdep_r32 eax ecx edx golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_pdep_r32(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

- byte0 is VEX escape 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is VEX escape 0xC4")
val result = emit_pdep_r32(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2

- byte1 is 0xE2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2")
val result = emit_pdep_r32(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)

- byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)")
# W=0, ~vvvv=14, L=0, pp=3 → 14*8+3=115
val result = emit_pdep_r32(0, 1, 2)
expect result[2] == 115
```

</details>

#### byte3 is opcode 0xF5

- byte3 is opcode 0xF5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xF5")
val result = emit_pdep_r32(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2

- byte4 is ModRM 0xC2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC2")
val result = emit_pdep_r32(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pdep_r32 extended src2 r9d

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

- byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)")
val result = emit_pdep_r32(0, 1, 9)
expect result[1] == 194
```

</details>

#### byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)

- byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x73 (W=0 ~vvvv=14 L=0 pp=3/F2)")
val result = emit_pdep_r32(0, 1, 9)
expect result[2] == 115
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

- byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)")
val result = emit_pdep_r32(0, 1, 9)
expect result[4] == 193
```

</details>

### BMI2 emit_pext_r64 rax rcx rdx golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_pext_r64(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

- byte0 is VEX escape 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is VEX escape 0xC4")
val result = emit_pext_r64(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2

- byte1 is 0xE2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2")
val result = emit_pext_r64(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)

- byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)")
# W=1, ~vvvv=14, L=0, pp=2(F3) → 128+14*8+2=242
val result = emit_pext_r64(0, 1, 2)
expect result[2] == 242
```

</details>

#### byte3 is opcode 0xF5

- byte3 is opcode 0xF5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xF5")
val result = emit_pext_r64(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2

- byte4 is ModRM 0xC2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC2")
val result = emit_pext_r64(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_pext_r64 extended dst r9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)")
val result = emit_pext_r64(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)

- byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xF2 (W=1 ~vvvv=14 L=0 pp=2/F3)")
val result = emit_pext_r64(9, 1, 2)
expect result[2] == 242
```

</details>

#### byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)

- byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xCA (mod=11 reg=1 rm=2)")
val result = emit_pext_r64(9, 1, 2)
expect result[4] == 202
```

</details>

### BMI2 emit_pext_r32 eax ecx edx golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_pext_r32(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte1 is 0xE2

- byte1 is 0xE2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2")
val result = emit_pext_r32(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x72 (W=0 ~vvvv=14 L=0 pp=2/F3)

- byte2 is 0x72 (W=0 ~vvvv=14 L=0 pp=2/F3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x72 (W=0 ~vvvv=14 L=0 pp=2/F3)")
# W=0, ~vvvv=14, L=0, pp=2(F3) → 14*8+2=114
val result = emit_pext_r32(0, 1, 2)
expect result[2] == 114
```

</details>

#### byte3 is opcode 0xF5

- byte3 is opcode 0xF5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xF5")
val result = emit_pext_r32(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC2

- byte4 is ModRM 0xC2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC2")
val result = emit_pext_r32(0, 1, 2)
expect result[4] == 194
```

</details>

### BMI2 emit_bzhi_r64 rax rcx rdx golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_bzhi_r64(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte0 is VEX escape 0xC4

- byte0 is VEX escape 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is VEX escape 0xC4")
val result = emit_bzhi_r64(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)")
# dst<8 → ~R=1; rm(src=1)<8 → ~B=1 → 226
val result = emit_bzhi_r64(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)

- byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)")
# W=1, ~vvvv=(15-idx=2)=13, L=0, pp=0(NP) → 128+13*8+0=232
val result = emit_bzhi_r64(0, 1, 2)
expect result[2] == 232
```

</details>

#### byte3 is opcode 0xF5

- byte3 is opcode 0xF5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xF5")
val result = emit_bzhi_r64(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

- byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)")
# mod=11, reg=dst%8=0, rm=src%8=1 → 192+0*8+1=193
val result = emit_bzhi_r64(0, 1, 2)
expect result[4] == 193
```

</details>

### BMI2 emit_bzhi_r64 extended dst r9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)")
# dst>=8 → ~R=0; rm(src=1)<8 → ~B=1 → 226-128=98
val result = emit_bzhi_r64(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)

- byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)")
val result = emit_bzhi_r64(9, 1, 2)
expect result[2] == 232
```

</details>

#### byte4 is ModRM 0xC9 (mod=11 reg=1 rm=1)

- byte4 is ModRM 0xC9 (mod=11 reg=1 rm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC9 (mod=11 reg=1 rm=1)")
# mod=11, reg=9%8=1, rm=1%8=1 → 192+1*8+1=201
val result = emit_bzhi_r64(9, 1, 2)
expect result[4] == 201
```

</details>

### BMI2 emit_bzhi_r64 extended idx r9

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)")
# rm(src=1)<8 → ~B=1 → 226
val result = emit_bzhi_r64(0, 1, 9)
expect result[1] == 226
```

</details>

#### byte2 is 0xB0 (W=1 ~vvvv=6 L=0 pp=0/NP)

- byte2 is 0xB0 (W=1 ~vvvv=6 L=0 pp=0/NP)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xB0 (W=1 ~vvvv=6 L=0 pp=0/NP)")
# W=1, ~vvvv=(15-idx=9)=6, L=0, pp=0(NP) → 128+6*8+0=176
val result = emit_bzhi_r64(0, 1, 9)
expect result[2] == 176
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

- byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)")
val result = emit_bzhi_r64(0, 1, 9)
expect result[4] == 193
```

</details>

### BMI2 emit_bzhi_r64 extended src r9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

- byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)")
# dst<8 → ~R=1; rm(src=9)>=8 → ~B=0 → 226-32=194
val result = emit_bzhi_r64(0, 9, 2)
expect result[1] == 194
```

</details>

#### byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)

- byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xE8 (W=1 ~vvvv=13 L=0 pp=0/NP)")
val result = emit_bzhi_r64(0, 9, 2)
expect result[2] == 232
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

- byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)")
# mod=11, reg=0%8=0, rm=9%8=1 → 192+0*8+1=193
val result = emit_bzhi_r64(0, 9, 2)
expect result[4] == 193
```

</details>

### BMI2 emit_bzhi_r32 eax ecx edx golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_bzhi_r32(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte1 is 0xE2

- byte1 is 0xE2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2")
val result = emit_bzhi_r32(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x68 (W=0 ~vvvv=13 L=0 pp=0/NP)

- byte2 is 0x68 (W=0 ~vvvv=13 L=0 pp=0/NP)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x68 (W=0 ~vvvv=13 L=0 pp=0/NP)")
# W=0, ~vvvv=(15-idx=2)=13, L=0, pp=0(NP) → 13*8+0=104
val result = emit_bzhi_r32(0, 1, 2)
expect result[2] == 104
```

</details>

#### byte3 is opcode 0xF5

- byte3 is opcode 0xF5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xF5")
val result = emit_bzhi_r32(0, 1, 2)
expect result[3] == 245
```

</details>

#### byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)

- byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC1 (mod=11 reg=0 rm=1)")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BMI2 emit_pdep_r64 rax rcx rdx golden, BMI2 emit_pdep_r64 extended dst r9, BMI2 emit_pdep_r64 extended src1 r9, BMI2 emit_pdep_r64 extended src2 r9, BMI2 emit_pdep_r32 eax ecx edx golden, BMI2 emit_pdep_r32 extended src2 r9d, BMI2 emit_pext_r64 rax rcx rdx golden, BMI2 emit_pext_r64 extended dst r9, BMI2 emit_pext_r32 eax ecx edx golden, BMI2 emit_bzhi_r64 rax rcx rdx golden, BMI2 emit_bzhi_r64 extended dst r9, BMI2 emit_bzhi_r64 extended idx r9, BMI2 emit_bzhi_r64 extended src r9, BMI2 emit_bzhi_r32 eax ecx edx golden.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af6665225b03de84bbd549ce410035afc395c0f0b5d6a63709abcb7a8fd0a181`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af6665225b03de84bbd549ce410035afc395c0f0b5d6a63709abcb7a8fd0a181`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af6665225b03de84bbd549ce410035afc395c0f0b5d6a63709abcb7a8fd0a181`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/x86_bmi2_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/x86_bmi2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/x86_bmi2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/x86_bmi2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/x86_bmi2_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 5 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/x86_bmi2_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte0 is VEX escape 0xC4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/x86_bmi2_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
