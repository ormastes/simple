# Avx2 Fp Emit Specification

> Tests covering AVX2 FP emit_vaddps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vaddps_ymm ymm3 ymm5 ymm7, AVX2 FP emit_vsubps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vsubps_ymm ymm2 ymm3 ymm4, AVX2 FP emit_vmulps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vmulps_ymm ymm1 ymm2 ymm3, AVX2 FP emit_vdivps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vdivps_ymm ymm4 ymm5 ymm6, AVX2 FP emit_vmaxps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vmaxps_ymm ymm1 ymm3 ymm5, AVX2 FP emit_vminps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vminps_ymm ymm2 ymm4 ymm6, AVX2 FP emit_vsqrtps_ymm ymm0 ymm0 golden, AVX2 FP emit_vsqrtps_ymm ymm3 ymm5, AVX2 FP emit_vrsqrtps_ymm ymm0 ymm0 golden, AVX2 FP emit_vrsqrtps_ymm ymm4 ymm6.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx2 Fp Emit Specification

## Scenarios

### AVX2 FP emit_vaddps_ymm ymm0 ymm0 ymm0 golden

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
val result = emit_vaddps_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte0 is VEX 3-byte escape 0xC4

- byte0 is VEX 3-byte escape 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is VEX 3-byte escape 0xC4")
val result = emit_vaddps_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)

- byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)")
val result = emit_vaddps_ymm(0, 0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x7C (W=0 ~vvvv=15 L=1 pp=00)

- byte2 is 0x7C (W=0 ~vvvv=15 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7C (W=0 ~vvvv=15 L=1 pp=00)")
val result = emit_vaddps_ymm(0, 0, 0)
expect result[2] == 124
```

</details>

#### byte3 is opcode 0x58

- byte3 is opcode 0x58


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x58")
val result = emit_vaddps_ymm(0, 0, 0)
expect result[3] == 88
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

- byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)")
val result = emit_vaddps_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vaddps_ymm ymm3 ymm5 ymm7

#### byte2 is 0x54 (W=0 ~vvvv=10 L=1 pp=00)

- byte2 is 0x54 (W=0 ~vvvv=10 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x54 (W=0 ~vvvv=10 L=1 pp=00)")
val result = emit_vaddps_ymm(3, 5, 7)
expect result[2] == 84
```

</details>

#### byte3 is opcode 0x58

- byte3 is opcode 0x58


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x58")
val result = emit_vaddps_ymm(3, 5, 7)
expect result[3] == 88
```

</details>

#### byte4 is ModRM 0xDF (mod=11 reg=3 rm=7)

- byte4 is ModRM 0xDF (mod=11 reg=3 rm=7)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xDF (mod=11 reg=3 rm=7)")
val result = emit_vaddps_ymm(3, 5, 7)
expect result[4] == 223
```

</details>

### AVX2 FP emit_vsubps_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vsubps_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

- byte0 is 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is 0xC4")
val result = emit_vsubps_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte2 is 0x7C (W=0 ~vvvv=15 L=1 pp=00)

- byte2 is 0x7C (W=0 ~vvvv=15 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7C (W=0 ~vvvv=15 L=1 pp=00)")
val result = emit_vsubps_ymm(0, 0, 0)
expect result[2] == 124
```

</details>

#### byte3 is opcode 0x5C

- byte3 is opcode 0x5C


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x5C")
val result = emit_vsubps_ymm(0, 0, 0)
expect result[3] == 92
```

</details>

#### byte4 is ModRM 0xC0

- byte4 is ModRM 0xC0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0")
val result = emit_vsubps_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vsubps_ymm ymm2 ymm3 ymm4

#### byte2 is 0x64 (W=0 ~vvvv=12 L=1 pp=00)

- byte2 is 0x64 (W=0 ~vvvv=12 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x64 (W=0 ~vvvv=12 L=1 pp=00)")
val result = emit_vsubps_ymm(2, 3, 4)
expect result[2] == 100
```

</details>

#### byte4 is ModRM 0xD4 (mod=11 reg=2 rm=4)

- byte4 is ModRM 0xD4 (mod=11 reg=2 rm=4)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xD4 (mod=11 reg=2 rm=4)")
val result = emit_vsubps_ymm(2, 3, 4)
expect result[4] == 212
```

</details>

### AVX2 FP emit_vmulps_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vmulps_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x59

- byte3 is opcode 0x59


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x59")
val result = emit_vmulps_ymm(0, 0, 0)
expect result[3] == 89
```

</details>

#### byte4 is ModRM 0xC0

- byte4 is ModRM 0xC0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0")
val result = emit_vmulps_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vmulps_ymm ymm1 ymm2 ymm3

#### byte2 is 0x6C (W=0 ~vvvv=13 L=1 pp=00)

- byte2 is 0x6C (W=0 ~vvvv=13 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x6C (W=0 ~vvvv=13 L=1 pp=00)")
val result = emit_vmulps_ymm(1, 2, 3)
expect result[2] == 108
```

</details>

#### byte4 is ModRM 0xCB (mod=11 reg=1 rm=3)

- byte4 is ModRM 0xCB (mod=11 reg=1 rm=3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xCB (mod=11 reg=1 rm=3)")
val result = emit_vmulps_ymm(1, 2, 3)
expect result[4] == 203
```

</details>

### AVX2 FP emit_vdivps_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vdivps_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x5E

- byte3 is opcode 0x5E


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x5E")
val result = emit_vdivps_ymm(0, 0, 0)
expect result[3] == 94
```

</details>

#### byte4 is ModRM 0xC0

- byte4 is ModRM 0xC0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0")
val result = emit_vdivps_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vdivps_ymm ymm4 ymm5 ymm6

#### byte2 is 0x54 (W=0 ~vvvv=10 L=1 pp=00)

- byte2 is 0x54 (W=0 ~vvvv=10 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x54 (W=0 ~vvvv=10 L=1 pp=00)")
val result = emit_vdivps_ymm(4, 5, 6)
expect result[2] == 84
```

</details>

#### byte4 is ModRM 0xE6 (mod=11 reg=4 rm=6)

- byte4 is ModRM 0xE6 (mod=11 reg=4 rm=6)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xE6 (mod=11 reg=4 rm=6)")
val result = emit_vdivps_ymm(4, 5, 6)
expect result[4] == 230
```

</details>

### AVX2 FP emit_vmaxps_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vmaxps_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x5F

- byte3 is opcode 0x5F


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x5F")
val result = emit_vmaxps_ymm(0, 0, 0)
expect result[3] == 95
```

</details>

#### byte4 is ModRM 0xC0

- byte4 is ModRM 0xC0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0")
val result = emit_vmaxps_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vmaxps_ymm ymm1 ymm3 ymm5

#### byte2 is 0x64 (W=0 ~vvvv=12 L=1 pp=00)

- byte2 is 0x64 (W=0 ~vvvv=12 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x64 (W=0 ~vvvv=12 L=1 pp=00)")
val result = emit_vmaxps_ymm(1, 3, 5)
expect result[2] == 100
```

</details>

#### byte4 is ModRM 0xCD (mod=11 reg=1 rm=5)

- byte4 is ModRM 0xCD (mod=11 reg=1 rm=5)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xCD (mod=11 reg=1 rm=5)")
val result = emit_vmaxps_ymm(1, 3, 5)
expect result[4] == 205
```

</details>

### AVX2 FP emit_vminps_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vminps_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x5D

- byte3 is opcode 0x5D


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x5D")
val result = emit_vminps_ymm(0, 0, 0)
expect result[3] == 93
```

</details>

#### byte4 is ModRM 0xC0

- byte4 is ModRM 0xC0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0")
val result = emit_vminps_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vminps_ymm ymm2 ymm4 ymm6

#### byte2 is 0x5C (W=0 ~vvvv=11 L=1 pp=00)

- byte2 is 0x5C (W=0 ~vvvv=11 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x5C (W=0 ~vvvv=11 L=1 pp=00)")
val result = emit_vminps_ymm(2, 4, 6)
expect result[2] == 92
```

</details>

#### byte4 is ModRM 0xD6 (mod=11 reg=2 rm=6)

- byte4 is ModRM 0xD6 (mod=11 reg=2 rm=6)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xD6 (mod=11 reg=2 rm=6)")
val result = emit_vminps_ymm(2, 4, 6)
expect result[4] == 214
```

</details>

### AVX2 FP emit_vsqrtps_ymm ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vsqrtps_ymm(0, 0)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

- byte0 is 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is 0xC4")
val result = emit_vsqrtps_ymm(0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)

- byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)")
val result = emit_vsqrtps_ymm(0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x7C (W=0 ~vvvv=1111 L=1 pp=00)

- byte2 is 0x7C (W=0 ~vvvv=1111 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7C (W=0 ~vvvv=1111 L=1 pp=00)")
val result = emit_vsqrtps_ymm(0, 0)
expect result[2] == 124
```

</details>

#### byte3 is opcode 0x51

- byte3 is opcode 0x51


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x51")
val result = emit_vsqrtps_ymm(0, 0)
expect result[3] == 81
```

</details>

#### byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)

- byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0 (mod=11 reg=0 rm=0)")
val result = emit_vsqrtps_ymm(0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vsqrtps_ymm ymm3 ymm5

#### byte2 is 0x7C (vvvv=1111 always for vsqrtps)

- byte2 is 0x7C (vvvv=1111 always for vsqrtps)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7C (vvvv=1111 always for vsqrtps)")
val result = emit_vsqrtps_ymm(3, 5)
expect result[2] == 124
```

</details>

#### byte4 is ModRM 0xDD (mod=11 reg=3 rm=5)

- byte4 is ModRM 0xDD (mod=11 reg=3 rm=5)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xDD (mod=11 reg=3 rm=5)")
val result = emit_vsqrtps_ymm(3, 5)
expect result[4] == 221
```

</details>

### AVX2 FP emit_vrsqrtps_ymm ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vrsqrtps_ymm(0, 0)
expect result.len() == 5
```

</details>

#### byte0 is 0xC4

- byte0 is 0xC4


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte0 is 0xC4")
val result = emit_vrsqrtps_ymm(0, 0)
expect result[0] == 196
```

</details>

#### byte2 is 0x7C (W=0 ~vvvv=1111 L=1 pp=00)

- byte2 is 0x7C (W=0 ~vvvv=1111 L=1 pp=00)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7C (W=0 ~vvvv=1111 L=1 pp=00)")
val result = emit_vrsqrtps_ymm(0, 0)
expect result[2] == 124
```

</details>

#### byte3 is opcode 0x52

- byte3 is opcode 0x52


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x52")
val result = emit_vrsqrtps_ymm(0, 0)
expect result[3] == 82
```

</details>

#### byte4 is ModRM 0xC0

- byte4 is ModRM 0xC0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xC0")
val result = emit_vrsqrtps_ymm(0, 0)
expect result[4] == 192
```

</details>

### AVX2 FP emit_vrsqrtps_ymm ymm4 ymm6

#### byte2 is 0x7C (vvvv=1111 always for vrsqrtps)

- byte2 is 0x7C (vvvv=1111 always for vrsqrtps)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7C (vvvv=1111 always for vrsqrtps)")
val result = emit_vrsqrtps_ymm(4, 6)
expect result[2] == 124
```

</details>

#### byte4 is ModRM 0xE6 (mod=11 reg=4 rm=6)

- byte4 is ModRM 0xE6 (mod=11 reg=4 rm=6)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xE6 (mod=11 reg=4 rm=6)")
val result = emit_vrsqrtps_ymm(4, 6)
expect result[4] == 230
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/avx2_fp_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AVX2 FP emit_vaddps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vaddps_ymm ymm3 ymm5 ymm7, AVX2 FP emit_vsubps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vsubps_ymm ymm2 ymm3 ymm4, AVX2 FP emit_vmulps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vmulps_ymm ymm1 ymm2 ymm3, AVX2 FP emit_vdivps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vdivps_ymm ymm4 ymm5 ymm6, AVX2 FP emit_vmaxps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vmaxps_ymm ymm1 ymm3 ymm5, AVX2 FP emit_vminps_ymm ymm0 ymm0 ymm0 golden, AVX2 FP emit_vminps_ymm ymm2 ymm4 ymm6, AVX2 FP emit_vsqrtps_ymm ymm0 ymm0 golden, AVX2 FP emit_vsqrtps_ymm ymm3 ymm5, AVX2 FP emit_vrsqrtps_ymm ymm0 ymm0 golden, AVX2 FP emit_vrsqrtps_ymm ymm4 ymm6.
- AVX2 FP emit_vaddps_ymm ymm0 ymm0 ymm0 golden
- AVX2 FP emit_vaddps_ymm ymm3 ymm5 ymm7
- AVX2 FP emit_vsubps_ymm ymm0 ymm0 ymm0 golden
- AVX2 FP emit_vsubps_ymm ymm2 ymm3 ymm4
- AVX2 FP emit_vmulps_ymm ymm0 ymm0 ymm0 golden
- AVX2 FP emit_vmulps_ymm ymm1 ymm2 ymm3
- AVX2 FP emit_vdivps_ymm ymm0 ymm0 ymm0 golden
- AVX2 FP emit_vdivps_ymm ymm4 ymm5 ymm6
- AVX2 FP emit_vmaxps_ymm ymm0 ymm0 ymm0 golden
- AVX2 FP emit_vmaxps_ymm ymm1 ymm3 ymm5
- AVX2 FP emit_vminps_ymm ymm0 ymm0 ymm0 golden
- AVX2 FP emit_vminps_ymm ymm2 ymm4 ymm6
- AVX2 FP emit_vsqrtps_ymm ymm0 ymm0 golden
- AVX2 FP emit_vsqrtps_ymm ymm3 ymm5
- AVX2 FP emit_vrsqrtps_ymm ymm0 ymm0 golden
- AVX2 FP emit_vrsqrtps_ymm ymm4 ymm6

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
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

- Canonical SPipe generation for source `4a308acb28ef72a83084875b81a4f1e3ffd85cfb67601b62e05a941b149aea15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a308acb28ef72a83084875b81a4f1e3ffd85cfb67601b62e05a941b149aea15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a308acb28ef72a83084875b81a4f1e3ffd85cfb67601b62e05a941b149aea15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/avx2_fp_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/avx2_fp_emit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/avx2_fp_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/avx2_fp_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/avx2_fp_emit_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 5 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx2_fp_emit_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte0 is VEX 3-byte escape 0xC4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx2_fp_emit_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
