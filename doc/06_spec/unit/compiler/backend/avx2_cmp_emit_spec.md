# Avx2 Cmp Emit Specification

> Tests covering AVX2 emit_vpcmpeqd_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpcmpeqd_ymm ymm3 ymm5 ymm7, AVX2 emit_vpcmpgtd_ymm ymm0 ymm1 ymm2 golden, AVX2 emit_vpcmpgtd_ymm ymm2 ymm4 ymm6, AVX2 emit_vpcmpeqb_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpcmpeqb_ymm ymm1 ymm2 ymm3, AVX2 emit_vpcmpgtb_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpcmpgtb_ymm ymm4 ymm3 ymm2, AVX2 emit_vpermd_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpermd_ymm ymm3 ymm5 ymm7, AVX2 emit_vpshufb_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpshufb_ymm ymm2 ymm1 ymm3, AVX2 emit_vpshufd_ymm ymm0 ymm0 imm=0 golden, AVX2 emit_vpshufd_ymm ymm3 ymm5 imm=0xAA.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx2 Cmp Emit Specification

## Scenarios

### AVX2 emit_vpcmpeqd_ymm ymm0 ymm0 ymm0 golden

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
val result = emit_vpcmpeqd_ymm(0, 0, 0)
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
val result = emit_vpcmpeqd_ymm(0, 0, 0)
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
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

- byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)")
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x76

- byte3 is opcode 0x76


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x76")
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[3] == 118
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
val result = emit_vpcmpeqd_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpcmpeqd_ymm ymm3 ymm5 ymm7

#### byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)

- byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)")
val result = emit_vpcmpeqd_ymm(3, 5, 7)
expect result[2] == 85
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
val result = emit_vpcmpeqd_ymm(3, 5, 7)
expect result[4] == 223
```

</details>

### AVX2 emit_vpcmpgtd_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vpcmpgtd_ymm(0, 1, 2)
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
val result = emit_vpcmpgtd_ymm(0, 1, 2)
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
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[1] == 225
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

- byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)")
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

#### byte3 is opcode 0x66

- byte3 is opcode 0x66


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x66")
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[3] == 102
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
val result = emit_vpcmpgtd_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### AVX2 emit_vpcmpgtd_ymm ymm2 ymm4 ymm6

#### byte2 is 0x5D (W=0 ~vvvv=11 L=1 pp=01)

- byte2 is 0x5D (W=0 ~vvvv=11 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x5D (W=0 ~vvvv=11 L=1 pp=01)")
val result = emit_vpcmpgtd_ymm(2, 4, 6)
expect result[2] == 93
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
val result = emit_vpcmpgtd_ymm(2, 4, 6)
expect result[4] == 214
```

</details>

### AVX2 emit_vpcmpeqb_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vpcmpeqb_ymm(0, 0, 0)
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
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE1

- byte1 is 0xE1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE1")
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

- byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)")
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x74

- byte3 is opcode 0x74


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x74")
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[3] == 116
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
val result = emit_vpcmpeqb_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpcmpeqb_ymm ymm1 ymm2 ymm3

#### byte2 is 0x6D (W=0 ~vvvv=13 L=1 pp=01)

- byte2 is 0x6D (W=0 ~vvvv=13 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x6D (W=0 ~vvvv=13 L=1 pp=01)")
val result = emit_vpcmpeqb_ymm(1, 2, 3)
expect result[2] == 109
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
val result = emit_vpcmpeqb_ymm(1, 2, 3)
expect result[4] == 203
```

</details>

### AVX2 emit_vpcmpgtb_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vpcmpgtb_ymm(0, 0, 0)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x64

- byte3 is opcode 0x64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x64")
val result = emit_vpcmpgtb_ymm(0, 0, 0)
expect result[3] == 100
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
val result = emit_vpcmpgtb_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpcmpgtb_ymm ymm4 ymm3 ymm2

#### byte2 is 0x65 (W=0 ~vvvv=12 L=1 pp=01)

- byte2 is 0x65 (W=0 ~vvvv=12 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x65 (W=0 ~vvvv=12 L=1 pp=01)")
val result = emit_vpcmpgtb_ymm(4, 3, 2)
expect result[2] == 101
```

</details>

#### byte4 is ModRM 0xE2 (mod=11 reg=4 rm=2)

- byte4 is ModRM 0xE2 (mod=11 reg=4 rm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xE2 (mod=11 reg=4 rm=2)")
val result = emit_vpcmpgtb_ymm(4, 3, 2)
expect result[4] == 226
```

</details>

### AVX2 emit_vpermd_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vpermd_ymm(0, 0, 0)
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
val result = emit_vpermd_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (0F38 map mmmmm=2)

- byte1 is 0xE2 (0F38 map mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (0F38 map mmmmm=2)")
val result = emit_vpermd_ymm(0, 0, 0)
expect result[1] == 226
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

- byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)")
val result = emit_vpermd_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x36

- byte3 is opcode 0x36


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x36")
val result = emit_vpermd_ymm(0, 0, 0)
expect result[3] == 54
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
val result = emit_vpermd_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpermd_ymm ymm3 ymm5 ymm7

#### byte1 is 0xE2 (0F38 map)

- byte1 is 0xE2 (0F38 map)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (0F38 map)")
val result = emit_vpermd_ymm(3, 5, 7)
expect result[1] == 226
```

</details>

#### byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)

- byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x55 (W=0 ~vvvv=10 L=1 pp=01)")
val result = emit_vpermd_ymm(3, 5, 7)
expect result[2] == 85
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
val result = emit_vpermd_ymm(3, 5, 7)
expect result[4] == 223
```

</details>

### AVX2 emit_vpshufb_ymm ymm0 ymm0 ymm0 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vpshufb_ymm(0, 0, 0)
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
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (0F38 map mmmmm=2)

- byte1 is 0xE2 (0F38 map mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (0F38 map mmmmm=2)")
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[1] == 226
```

</details>

#### byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)

- byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x7D (W=0 ~vvvv=15 L=1 pp=01)")
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[2] == 125
```

</details>

#### byte3 is opcode 0x00

- byte3 is opcode 0x00


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x00")
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[3] == 0
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
val result = emit_vpshufb_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

### AVX2 emit_vpshufb_ymm ymm2 ymm1 ymm3

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

- byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)")
val result = emit_vpshufb_ymm(2, 1, 3)
expect result[2] == 117
```

</details>

#### byte4 is ModRM 0xD3 (mod=11 reg=2 rm=3)

- byte4 is ModRM 0xD3 (mod=11 reg=2 rm=3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte4 is ModRM 0xD3 (mod=11 reg=2 rm=3)")
val result = emit_vpshufb_ymm(2, 1, 3)
expect result[4] == 211
```

</details>

### AVX2 emit_vpshufd_ymm ymm0 ymm0 imm=0 golden

#### emits 6 bytes

- emits 6 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 6 bytes")
val result = emit_vpshufd_ymm(0, 0, 0)
expect result.len() == 6
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
val result = emit_vpshufd_ymm(0, 0, 0)
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
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[1] == 225
```

</details>

#### byte2 is 0x05 (vvvv=1111 W=0 L=1 pp=01)

- byte2 is 0x05 (vvvv=1111 W=0 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x05 (vvvv=1111 W=0 L=1 pp=01)")
# vvvv=15 → ~vvvv=0 → 0*8+5=5
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[2] == 5
```

</details>

#### byte3 is opcode 0x70

- byte3 is opcode 0x70


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x70")
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[3] == 112
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
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[4] == 192
```

</details>

#### byte5 is imm8 0

- byte5 is imm8 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte5 is imm8 0")
val result = emit_vpshufd_ymm(0, 0, 0)
expect result[5] == 0
```

</details>

### AVX2 emit_vpshufd_ymm ymm3 ymm5 imm=0xAA

#### byte2 is 0x05 (vvvv=1111 always)

- byte2 is 0x05 (vvvv=1111 always)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x05 (vvvv=1111 always)")
val result = emit_vpshufd_ymm(3, 5, 170)
expect result[2] == 5
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
val result = emit_vpshufd_ymm(3, 5, 170)
expect result[4] == 221
```

</details>

#### byte5 is imm8 0xAA

- byte5 is imm8 0xAA


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte5 is imm8 0xAA")
val result = emit_vpshufd_ymm(3, 5, 170)
expect result[5] == 170
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/avx2_cmp_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AVX2 emit_vpcmpeqd_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpcmpeqd_ymm ymm3 ymm5 ymm7, AVX2 emit_vpcmpgtd_ymm ymm0 ymm1 ymm2 golden, AVX2 emit_vpcmpgtd_ymm ymm2 ymm4 ymm6, AVX2 emit_vpcmpeqb_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpcmpeqb_ymm ymm1 ymm2 ymm3, AVX2 emit_vpcmpgtb_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpcmpgtb_ymm ymm4 ymm3 ymm2, AVX2 emit_vpermd_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpermd_ymm ymm3 ymm5 ymm7, AVX2 emit_vpshufb_ymm ymm0 ymm0 ymm0 golden, AVX2 emit_vpshufb_ymm ymm2 ymm1 ymm3, AVX2 emit_vpshufd_ymm ymm0 ymm0 imm=0 golden, AVX2 emit_vpshufd_ymm ymm3 ymm5 imm=0xAA.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3627280510c93068b730427c01f476abec89ba25e0abfd81d49d2871404a754a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3627280510c93068b730427c01f476abec89ba25e0abfd81d49d2871404a754a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3627280510c93068b730427c01f476abec89ba25e0abfd81d49d2871404a754a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/avx2_cmp_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/avx2_cmp_emit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/avx2_cmp_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/avx2_cmp_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/avx2_cmp_emit_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 5 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx2_cmp_emit_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte0 is VEX 3-byte escape 0xC4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx2_cmp_emit_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte1 is 0xE1 (~R=1 ~X=1 ~B=1 mmmmm=1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
