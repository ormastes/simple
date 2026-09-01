# Fma3 Emit Specification

> Tests covering FMA3 emit_vfmadd132ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmadd132ps_ymm extended rd ymm9, FMA3 emit_vfmadd132ps_ymm extended rn ymm9, FMA3 emit_vfmadd132ps_ymm extended rm ymm9, FMA3 emit_vfmadd213ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmadd213ps_ymm extended rm ymm9, FMA3 emit_vfmadd231ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub132ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub132ps_ymm extended rd ymm9, FMA3 emit_vfmsub213ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub231ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub231ps_ymm extended rd ymm9, FMA3 emit_vfnmadd213ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfnmadd213ps_ymm extended rn ymm9, FMA3 emit_vfmadd132pd_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmadd132pd_ymm extended rd ymm9.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fma3 Emit Specification

## Scenarios

### FMA3 emit_vfmadd132ps_ymm ymm0 ymm1 ymm2 golden

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
val result = emit_vfmadd132ps_ymm(0, 1, 2)
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
val result = emit_vfmadd132ps_ymm(0, 1, 2)
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
# rd<8 → ~R=1, rm<8 → ~B=1, ~X=1, mmmmm=2 → 226
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)

- byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x75 (W=0 ~vvvv=14 L=1 pp=01)")
# W=0, ~vvvv=(15-rn=1)=14, L=1(bit2=4), pp=01(1) → 14*8+5=117
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

#### byte3 is opcode 0x98

- byte3 is opcode 0x98


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x98")
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[3] == 152
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
# mod=11, reg=rd%8=0, rm=rm%8=2 → 192+0*8+2=194
val result = emit_vfmadd132ps_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132ps_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)")
# rd>=8 → ~R=0, rm<8 → ~B=1 → 226-128=98
val result = emit_vfmadd132ps_ymm(9, 1, 2)
expect result[1] == 98
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
val result = emit_vfmadd132ps_ymm(9, 1, 2)
expect result[2] == 117
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
val result = emit_vfmadd132ps_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

### FMA3 emit_vfmadd132ps_ymm extended rn ymm9

#### byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)

- byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)")
# ~vvvv=(15-rn=9)=6, L=1, pp=01 → 6*8+5=53
val result = emit_vfmadd132ps_ymm(0, 9, 2)
expect result[2] == 53
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
val result = emit_vfmadd132ps_ymm(0, 9, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132ps_ymm extended rm ymm9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

- byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)")
# rd<8 → ~R=1; rm>=8 → ~B=0 → 226-32=194
val result = emit_vfmadd132ps_ymm(0, 1, 9)
expect result[1] == 194
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
val result = emit_vfmadd132ps_ymm(0, 1, 9)
expect result[4] == 193
```

</details>

### FMA3 emit_vfmadd213ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vfmadd213ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xA8

- byte3 is opcode 0xA8


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xA8")
val result = emit_vfmadd213ps_ymm(0, 1, 2)
expect result[3] == 168
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
val result = emit_vfmadd213ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmadd213ps_ymm extended rm ymm9

#### byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)

- byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xC2 (~R=1 ~X=1 ~B=0 mmmmm=2)")
val result = emit_vfmadd213ps_ymm(0, 1, 9)
expect result[1] == 194
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
val result = emit_vfmadd213ps_ymm(0, 1, 9)
expect result[4] == 193
```

</details>

### FMA3 emit_vfmadd231ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vfmadd231ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xB8

- byte3 is opcode 0xB8


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xB8")
val result = emit_vfmadd231ps_ymm(0, 1, 2)
expect result[3] == 184
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
val result = emit_vfmadd231ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub132ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vfmsub132ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0x9A

- byte3 is opcode 0x9A


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x9A")
val result = emit_vfmsub132ps_ymm(0, 1, 2)
expect result[3] == 154
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
val result = emit_vfmsub132ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub132ps_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)")
val result = emit_vfmsub132ps_ymm(9, 1, 2)
expect result[1] == 98
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
val result = emit_vfmsub132ps_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

### FMA3 emit_vfmsub213ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vfmsub213ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xAA

- byte3 is opcode 0xAA


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xAA")
val result = emit_vfmsub213ps_ymm(0, 1, 2)
expect result[3] == 170
```

</details>

#### byte2 is 0x75

- byte2 is 0x75


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x75")
val result = emit_vfmsub213ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub231ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vfmsub231ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xBA

- byte3 is opcode 0xBA


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xBA")
val result = emit_vfmsub231ps_ymm(0, 1, 2)
expect result[3] == 186
```

</details>

#### byte2 is 0x75

- byte2 is 0x75


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x75")
val result = emit_vfmsub231ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfmsub231ps_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)")
val result = emit_vfmsub231ps_ymm(9, 1, 2)
expect result[1] == 98
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
val result = emit_vfmsub231ps_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

### FMA3 emit_vfnmadd213ps_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vfnmadd213ps_ymm(0, 1, 2)
expect result.len() == 5
```

</details>

#### byte3 is opcode 0xAC

- byte3 is opcode 0xAC


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0xAC")
val result = emit_vfnmadd213ps_ymm(0, 1, 2)
expect result[3] == 172
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
val result = emit_vfnmadd213ps_ymm(0, 1, 2)
expect result[2] == 117
```

</details>

### FMA3 emit_vfnmadd213ps_ymm extended rn ymm9

#### byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)

- byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0x35 (W=0 ~vvvv=6 L=1 pp=01)")
# ~vvvv=(15-rn=9)=6 → 6*8+5=53
val result = emit_vfnmadd213ps_ymm(0, 9, 2)
expect result[2] == 53
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
val result = emit_vfnmadd213ps_ymm(0, 9, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132pd_ymm ymm0 ymm1 ymm2 golden

#### emits 5 bytes

- emits 5 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 5 bytes")
val result = emit_vfmadd132pd_ymm(0, 1, 2)
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
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[0] == 196
```

</details>

#### byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)")
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[1] == 226
```

</details>

#### byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)

- byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)")
# W=1 adds 128, ~vvvv=14, L=1, pp=01 → 128+14*8+5=245
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[2] == 245
```

</details>

#### byte3 is opcode 0x98

- byte3 is opcode 0x98


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte3 is opcode 0x98")
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[3] == 152
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
val result = emit_vfmadd132pd_ymm(0, 1, 2)
expect result[4] == 194
```

</details>

### FMA3 emit_vfmadd132pd_ymm extended rd ymm9

#### byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)

- byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte1 is 0x62 (~R=0 ~X=1 ~B=1 mmmmm=2)")
# rd>=8 → ~R=0 → 226-128=98
val result = emit_vfmadd132pd_ymm(9, 1, 2)
expect result[1] == 98
```

</details>

#### byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)

- byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte2 is 0xF5 (W=1 ~vvvv=14 L=1 pp=01)")
val result = emit_vfmadd132pd_ymm(9, 1, 2)
expect result[2] == 245
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
val result = emit_vfmadd132pd_ymm(9, 1, 2)
expect result[4] == 202
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/fma3_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FMA3 emit_vfmadd132ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmadd132ps_ymm extended rd ymm9, FMA3 emit_vfmadd132ps_ymm extended rn ymm9, FMA3 emit_vfmadd132ps_ymm extended rm ymm9, FMA3 emit_vfmadd213ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmadd213ps_ymm extended rm ymm9, FMA3 emit_vfmadd231ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub132ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub132ps_ymm extended rd ymm9, FMA3 emit_vfmsub213ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub231ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmsub231ps_ymm extended rd ymm9, FMA3 emit_vfnmadd213ps_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfnmadd213ps_ymm extended rn ymm9, FMA3 emit_vfmadd132pd_ymm ymm0 ymm1 ymm2 golden, FMA3 emit_vfmadd132pd_ymm extended rd ymm9.
- FMA3 emit_vfmadd132ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmadd132ps_ymm extended rd ymm9
- FMA3 emit_vfmadd132ps_ymm extended rn ymm9
- FMA3 emit_vfmadd132ps_ymm extended rm ymm9
- FMA3 emit_vfmadd213ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmadd213ps_ymm extended rm ymm9
- FMA3 emit_vfmadd231ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub132ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub132ps_ymm extended rd ymm9
- FMA3 emit_vfmsub213ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub231ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmsub231ps_ymm extended rd ymm9
- FMA3 emit_vfnmadd213ps_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfnmadd213ps_ymm extended rn ymm9
- FMA3 emit_vfmadd132pd_ymm ymm0 ymm1 ymm2 golden
- FMA3 emit_vfmadd132pd_ymm extended rd ymm9

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
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

- Canonical SPipe generation for source `17d1203d7a2a507a878b510028ae797b564dc6f57e510c17013b4d97a9499adf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17d1203d7a2a507a878b510028ae797b564dc6f57e510c17013b4d97a9499adf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17d1203d7a2a507a878b510028ae797b564dc6f57e510c17013b4d97a9499adf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/fma3_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/fma3_emit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/fma3_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/fma3_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/fma3_emit_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 5 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/fma3_emit_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte0 is VEX escape 0xC4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/fma3_emit_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'byte1 is 0xE2 (~R=1 ~X=1 ~B=1 mmmmm=2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
