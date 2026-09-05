# avx512_gather_scatter_spec

> Purpose: Prove that AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 no-disp.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_gather_scatter_spec

Purpose: Prove that AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 no-disp.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_gather_scatter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 no-disp.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 no-disp

#### VPGATHERDD Z0 k1 rax Z1*4 emits 7 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VPGATHERDD Z0 k1 rax Z1*4 emits 7 bytes
- Verify: VPGATHERDD Z0 k1 rax Z1*4 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 emits 7 bytes")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 emits 7 bytes")
# @req: REQ-COMP-AVX-512-VPGATHERDD-ZMM0-K1-RAX-ZMM1-SCAL-001
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 escape is 0x62

- VPGATHERDD Z0 k1 rax Z1*4 escape is 0x62
- Verify: VPGATHERDD Z0 k1 rax Z1*4 escape is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 escape is 0x62")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 escape is 0x62")
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[0]).to_equal(98)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 P0 is 0xF2

- VPGATHERDD Z0 k1 rax Z1*4 P0 is 0xF2
- Verify: VPGATHERDD Z0 k1 rax Z1*4 P0 is 0xF2
   - Expected: result[1] equals `242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 P0 is 0xF2")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 P0 is 0xF2")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm=010 (0F38) = 11110010 = 0xF2 = 242
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[1]).to_equal(242)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 P1 is 0x7D

- VPGATHERDD Z0 k1 rax Z1*4 P1 is 0x7D
- Verify: VPGATHERDD Z0 k1 rax Z1*4 P1 is 0x7D
   - Expected: result[2] equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 P1 is 0x7D")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 P1 is 0x7D")
# P1: W=0 ~vvvv=1111 must-1=1 pp=01 = 01111101 = 0x7D = 125
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[2]).to_equal(125)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 P2 is 0x49

- VPGATHERDD Z0 k1 rax Z1*4 P2 is 0x49
- Verify: VPGATHERDD Z0 k1 rax Z1*4 P2 is 0x49
   - Expected: result[3] equals `73`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 P2 is 0x49")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 P2 is 0x49")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=001 = 01001001 = 0x49 = 73
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[3]).to_equal(73)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 opcode is 0x90

- VPGATHERDD Z0 k1 rax Z1*4 opcode is 0x90
- Verify: VPGATHERDD Z0 k1 rax Z1*4 opcode is 0x90
   - Expected: result[4] equals `144`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 opcode is 0x90")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 opcode is 0x90")
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[4]).to_equal(144)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 ModRM is 0x04

- VPGATHERDD Z0 k1 rax Z1*4 ModRM is 0x04
- Verify: VPGATHERDD Z0 k1 rax Z1*4 ModRM is 0x04
   - Expected: result[5] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 ModRM is 0x04")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 ModRM is 0x04")
# ModRM: mod=00 reg=000(zmm0) rm=100(SIB) = 00000100 = 0x04 = 4
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[5]).to_equal(4)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 SIB is 0x88

- VPGATHERDD Z0 k1 rax Z1*4 SIB is 0x88
- Verify: VPGATHERDD Z0 k1 rax Z1*4 SIB is 0x88
   - Expected: result[6] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4 SIB is 0x88")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4 SIB is 0x88")
# SIB: ss=10(x4) idx=001(zmm1) base=000(rax) = 10001000 = 0x88 = 136
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 disp8

#### VPGATHERDD Z0 k1 rax Z1*4+8 emits 8 bytes

- VPGATHERDD Z0 k1 rax Z1*4+8 emits 8 bytes
- Verify: VPGATHERDD Z0 k1 rax Z1*4+8 emits 8 bytes
   - Expected: result.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4+8 emits 8 bytes")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4+8 emits 8 bytes")
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result.len()).to_equal(8)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4+8 ModRM is 0x44

- VPGATHERDD Z0 k1 rax Z1*4+8 ModRM is 0x44
- Verify: VPGATHERDD Z0 k1 rax Z1*4+8 ModRM is 0x44
   - Expected: result[5] equals `68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4+8 ModRM is 0x44")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4+8 ModRM is 0x44")
# mod=01 = disp8 present
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result[5]).to_equal(68)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4+8 SIB is 0x88

- VPGATHERDD Z0 k1 rax Z1*4+8 SIB is 0x88
- Verify: VPGATHERDD Z0 k1 rax Z1*4+8 SIB is 0x88
   - Expected: result[6] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4+8 SIB is 0x88")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4+8 SIB is 0x88")
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result[6]).to_equal(136)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4+8 disp8 is 0x02

- VPGATHERDD Z0 k1 rax Z1*4+8 disp8 is 0x02
- Verify: VPGATHERDD Z0 k1 rax Z1*4+8 disp8 is 0x02
   - Expected: result[7] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k1 rax Z1*4+8 disp8 is 0x02")
step("Verify: VPGATHERDD Z0 k1 rax Z1*4+8 disp8 is 0x02")
# disp8 = 8/4 = 2 (EVEX disp8*N compressed, N=4)
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result[7]).to_equal(2)
```

</details>

### AVX-512 VPGATHERDD zmm0 k7 rax zmm1 scale4

#### VPGATHERDD Z0 k7 rax Z1*4 emits 7 bytes

- VPGATHERDD Z0 k7 rax Z1*4 emits 7 bytes
- Verify: VPGATHERDD Z0 k7 rax Z1*4 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k7 rax Z1*4 emits 7 bytes")
step("Verify: VPGATHERDD Z0 k7 rax Z1*4 emits 7 bytes")
val result = emit_avx512_vpgatherdd_zmm(48, 87, 49, 0, 4, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPGATHERDD Z0 k7 rax Z1*4 P2 is 0x4F

- VPGATHERDD Z0 k7 rax Z1*4 P2 is 0x4F
- Verify: VPGATHERDD Z0 k7 rax Z1*4 P2 is 0x4F
   - Expected: result[3] equals `79`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z0 k7 rax Z1*4 P2 is 0x4F")
step("Verify: VPGATHERDD Z0 k7 rax Z1*4 P2 is 0x4F")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=111 = 01001111 = 0x4F = 79
val result = emit_avx512_vpgatherdd_zmm(48, 87, 49, 0, 4, 0)
expect(result[3]).to_equal(79)
```

</details>

### AVX-512 VPSCATTERDD rax zmm1 scale4 k1 zmm0

#### VPSCATTERDD k1 rax Z1*4 Z0 emits 7 bytes

- VPSCATTERDD k1 rax Z1*4 Z0 emits 7 bytes
- Verify: VPSCATTERDD k1 rax Z1*4 Z0 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPSCATTERDD k1 rax Z1*4 Z0 emits 7 bytes")
step("Verify: VPSCATTERDD k1 rax Z1*4 Z0 emits 7 bytes")
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result.len()).to_equal(7)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 escape is 0x62

- VPSCATTERDD k1 rax Z1*4 Z0 escape is 0x62
- Verify: VPSCATTERDD k1 rax Z1*4 Z0 escape is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPSCATTERDD k1 rax Z1*4 Z0 escape is 0x62")
step("Verify: VPSCATTERDD k1 rax Z1*4 Z0 escape is 0x62")
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[0]).to_equal(98)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 P0 is 0xF2

- VPSCATTERDD k1 rax Z1*4 Z0 P0 is 0xF2
- Verify: VPSCATTERDD k1 rax Z1*4 Z0 P0 is 0xF2
   - Expected: result[1] equals `242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPSCATTERDD k1 rax Z1*4 Z0 P0 is 0xF2")
step("Verify: VPSCATTERDD k1 rax Z1*4 Z0 P0 is 0xF2")
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[1]).to_equal(242)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 opcode is 0xA0

- VPSCATTERDD k1 rax Z1*4 Z0 opcode is 0xA0
- Verify: VPSCATTERDD k1 rax Z1*4 Z0 opcode is 0xA0
   - Expected: result[4] equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPSCATTERDD k1 rax Z1*4 Z0 opcode is 0xA0")
step("Verify: VPSCATTERDD k1 rax Z1*4 Z0 opcode is 0xA0")
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[4]).to_equal(160)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 SIB is 0x88

- VPSCATTERDD k1 rax Z1*4 Z0 SIB is 0x88
- Verify: VPSCATTERDD k1 rax Z1*4 Z0 SIB is 0x88
   - Expected: result[6] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPSCATTERDD k1 rax Z1*4 Z0 SIB is 0x88")
step("Verify: VPSCATTERDD k1 rax Z1*4 Z0 SIB is 0x88")
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VGATHERDPS zmm0 k1 rax zmm1 scale4

#### VGATHERDPS Z0 k1 rax Z1*4 emits 7 bytes

- VGATHERDPS Z0 k1 rax Z1*4 emits 7 bytes
- Verify: VGATHERDPS Z0 k1 rax Z1*4 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VGATHERDPS Z0 k1 rax Z1*4 emits 7 bytes")
step("Verify: VGATHERDPS Z0 k1 rax Z1*4 emits 7 bytes")
val result = emit_avx512_vgatherdps_zmm(48, 81, 49, 0, 4, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VGATHERDPS Z0 k1 rax Z1*4 opcode is 0x92

- VGATHERDPS Z0 k1 rax Z1*4 opcode is 0x92
- Verify: VGATHERDPS Z0 k1 rax Z1*4 opcode is 0x92
   - Expected: result[4] equals `146`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VGATHERDPS Z0 k1 rax Z1*4 opcode is 0x92")
step("Verify: VGATHERDPS Z0 k1 rax Z1*4 opcode is 0x92")
val result = emit_avx512_vgatherdps_zmm(48, 81, 49, 0, 4, 0)
expect(result[4]).to_equal(146)
```

</details>

#### VGATHERDPS Z0 k1 rax Z1*4 SIB is 0x88

- VGATHERDPS Z0 k1 rax Z1*4 SIB is 0x88
- Verify: VGATHERDPS Z0 k1 rax Z1*4 SIB is 0x88
   - Expected: result[6] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VGATHERDPS Z0 k1 rax Z1*4 SIB is 0x88")
step("Verify: VGATHERDPS Z0 k1 rax Z1*4 SIB is 0x88")
val result = emit_avx512_vgatherdps_zmm(48, 81, 49, 0, 4, 0)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VSCATTERDPS rax zmm1 scale4 k1 zmm0

#### VSCATTERDPS k1 rax Z1*4 Z0 emits 7 bytes

- VSCATTERDPS k1 rax Z1*4 Z0 emits 7 bytes
- Verify: VSCATTERDPS k1 rax Z1*4 Z0 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VSCATTERDPS k1 rax Z1*4 Z0 emits 7 bytes")
step("Verify: VSCATTERDPS k1 rax Z1*4 Z0 emits 7 bytes")
val result = emit_avx512_vscatterdps_zmm(81, 49, 0, 4, 0, 48)
expect(result.len()).to_equal(7)
```

</details>

#### VSCATTERDPS k1 rax Z1*4 Z0 opcode is 0xA2

- VSCATTERDPS k1 rax Z1*4 Z0 opcode is 0xA2
- Verify: VSCATTERDPS k1 rax Z1*4 Z0 opcode is 0xA2
   - Expected: result[4] equals `162`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VSCATTERDPS k1 rax Z1*4 Z0 opcode is 0xA2")
step("Verify: VSCATTERDPS k1 rax Z1*4 Z0 opcode is 0xA2")
val result = emit_avx512_vscatterdps_zmm(81, 49, 0, 4, 0, 48)
expect(result[4]).to_equal(162)
```

</details>

#### VSCATTERDPS k1 rax Z1*4 Z0 SIB is 0x88

- VSCATTERDPS k1 rax Z1*4 Z0 SIB is 0x88
- Verify: VSCATTERDPS k1 rax Z1*4 Z0 SIB is 0x88
   - Expected: result[6] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VSCATTERDPS k1 rax Z1*4 Z0 SIB is 0x88")
step("Verify: VSCATTERDPS k1 rax Z1*4 Z0 SIB is 0x88")
val result = emit_avx512_vscatterdps_zmm(81, 49, 0, 4, 0, 48)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VPGATHERDD scale boundary SIB tests

#### VPGATHERDD scale=1 SIB is 0x08

- VPGATHERDD scale=1 SIB is 0x08
- Verify: VPGATHERDD scale=1 SIB is 0x08
   - Expected: result[6] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD scale=1 SIB is 0x08")
step("Verify: VPGATHERDD scale=1 SIB is 0x08")
# SIB: ss=00(x1) idx=001(zmm1) base=000(rax) = 00001000 = 0x08 = 8
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 1, 0)
expect(result[6]).to_equal(8)
```

</details>

#### VPGATHERDD scale=2 SIB is 0x48

- VPGATHERDD scale=2 SIB is 0x48
- Verify: VPGATHERDD scale=2 SIB is 0x48
   - Expected: result[6] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD scale=2 SIB is 0x48")
step("Verify: VPGATHERDD scale=2 SIB is 0x48")
# SIB: ss=01(x2) idx=001(zmm1) base=000(rax) = 01001000 = 0x48 = 72
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 2, 0)
expect(result[6]).to_equal(72)
```

</details>

#### VPGATHERDD scale=4 SIB is 0x88

- VPGATHERDD scale=4 SIB is 0x88
- Verify: VPGATHERDD scale=4 SIB is 0x88
   - Expected: result[6] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD scale=4 SIB is 0x88")
step("Verify: VPGATHERDD scale=4 SIB is 0x88")
# SIB: ss=10(x4) idx=001(zmm1) base=000(rax) = 10001000 = 0x88 = 136
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[6]).to_equal(136)
```

</details>

#### VPGATHERDD scale=8 SIB is 0xC8

- VPGATHERDD scale=8 SIB is 0xC8
- Verify: VPGATHERDD scale=8 SIB is 0xC8
   - Expected: result[6] equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD scale=8 SIB is 0xC8")
step("Verify: VPGATHERDD scale=8 SIB is 0xC8")
# SIB: ss=11(x8) idx=001(zmm1) base=000(rax) = 11001000 = 0xC8 = 200
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 8, 0)
expect(result[6]).to_equal(200)
```

</details>

### AVX-512 gather k0 rejection guard

#### VPGATHERDD with k0 returns empty (k0 forbidden)

- VPGATHERDD with k0 returns empty (k0 forbidden)
- Verify: VPGATHERDD with k0 returns empty (k0 forbidden)
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD with k0 returns empty (k0 forbidden)")
step("Verify: VPGATHERDD with k0 returns empty (k0 forbidden)")
val result = emit_avx512_vpgatherdd_zmm(48, 80, 49, 0, 4, 0)
expect(result.len()).to_equal(0)
```

</details>

#### VPSCATTERDD with k0 returns empty (k0 forbidden)

- VPSCATTERDD with k0 returns empty (k0 forbidden)
- Verify: VPSCATTERDD with k0 returns empty (k0 forbidden)
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPSCATTERDD with k0 returns empty (k0 forbidden)")
step("Verify: VPSCATTERDD with k0 returns empty (k0 forbidden)")
val result = emit_avx512_vpscatterdd_zmm(80, 49, 0, 4, 0, 48)
expect(result.len()).to_equal(0)
```

</details>

### AVX-512 VPGATHERDD zmm1 k1 rax zmm0 scale4 swapped

#### VPGATHERDD Z1 k1 rax Z0*4 ModRM is 0x0C

- VPGATHERDD Z1 k1 rax Z0*4 ModRM is 0x0C
- Verify: VPGATHERDD Z1 k1 rax Z0*4 ModRM is 0x0C
   - Expected: result[5] equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z1 k1 rax Z0*4 ModRM is 0x0C")
step("Verify: VPGATHERDD Z1 k1 rax Z0*4 ModRM is 0x0C")
# ModRM: mod=00 reg=001(zmm1) rm=100(SIB) = 00001100 = 0x0C = 12
val result = emit_avx512_vpgatherdd_zmm(49, 81, 48, 0, 4, 0)
expect(result[5]).to_equal(12)
```

</details>

#### VPGATHERDD Z1 k1 rax Z0*4 SIB is 0x80

- VPGATHERDD Z1 k1 rax Z0*4 SIB is 0x80
- Verify: VPGATHERDD Z1 k1 rax Z0*4 SIB is 0x80
   - Expected: result[6] equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPGATHERDD Z1 k1 rax Z0*4 SIB is 0x80")
step("Verify: VPGATHERDD Z1 k1 rax Z0*4 SIB is 0x80")
# SIB: ss=10(x4) idx=000(zmm0) base=000(rax) = 10000000 = 0x80 = 128
val result = emit_avx512_vpgatherdd_zmm(49, 81, 48, 0, 4, 0)
expect(result[6]).to_equal(128)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-AVX-512-VPGATHERDD-ZMM0-K1-RAX-ZMM1-SCAL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c93f7a6b4c50a87dd6593181eff80d53571515e64757ff501d4893c8d91939c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c93f7a6b4c50a87dd6593181eff80d53571515e64757ff501d4893c8d91939c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c93f7a6b4c50a87dd6593181eff80d53571515e64757ff501d4893c8d91939c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/avx512_gather_scatter_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/avx512_gather_scatter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/avx512_gather_scatter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/avx512_gather_scatter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/avx512_gather_scatter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 33 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/avx512_gather_scatter_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPGATHERDD Z0 k1 rax Z1*4 emits 7 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/avx512_gather_scatter_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPGATHERDD Z0 k1 rax Z1*4 escape is 0x62' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/avx512_gather_scatter_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPGATHERDD Z0 k1 rax Z1*4 P0 is 0xF2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
