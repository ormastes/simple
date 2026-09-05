# avx512_reduction_emit_spec

> Purpose: Prove that AVX-512 emit VBROADCASTSS zmm0 from xmm0 golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_reduction_emit_spec

Purpose: Prove that AVX-512 emit VBROADCASTSS zmm0 from xmm0 golden.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/avx512_reduction_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AVX-512 emit VBROADCASTSS zmm0 from xmm0 golden.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AVX-512 emit VBROADCASTSS zmm0 from xmm0 golden

#### VBROADCASTSS Z0 X0 emits 6 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VBROADCASTSS Z0 X0 emits 6 bytes
- Verify: VBROADCASTSS Z0 X0 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z0 X0 emits 6 bytes")
step("Verify: VBROADCASTSS Z0 X0 emits 6 bytes")
# @req: REQ-COMP-AVX-512-EMIT-VBROADCASTSS-ZMM0-FROM-XMM0-001
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result.len()).to_equal(6)
```

</details>

#### VBROADCASTSS Z0 X0 escape byte is 0x62

- VBROADCASTSS Z0 X0 escape byte is 0x62
- Verify: VBROADCASTSS Z0 X0 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z0 X0 escape byte is 0x62")
step("Verify: VBROADCASTSS Z0 X0 escape byte is 0x62")
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[0]).to_equal(98)
```

</details>

#### VBROADCASTSS Z0 X0 P0 is 0xF2

- VBROADCASTSS Z0 X0 P0 is 0xF2
- Verify: VBROADCASTSS Z0 X0 P0 is 0xF2
   - Expected: result[1] equals `242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z0 X0 P0 is 0xF2")
step("Verify: VBROADCASTSS Z0 X0 P0 is 0xF2")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm=010(0F38) = 0xF2
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[1]).to_equal(242)
```

</details>

#### VBROADCASTSS Z0 X0 P1 is 0x7D

- VBROADCASTSS Z0 X0 P1 is 0x7D
- Verify: VBROADCASTSS Z0 X0 P1 is 0x7D
   - Expected: result[2] equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z0 X0 P1 is 0x7D")
step("Verify: VBROADCASTSS Z0 X0 P1 is 0x7D")
# P1: W=0 ~vvvv=1111(unused) must-1 pp=01(0x66) = 0x7D
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[2]).to_equal(125)
```

</details>

#### VBROADCASTSS Z0 X0 P2 is 0x48

- VBROADCASTSS Z0 X0 P2 is 0x48
- Verify: VBROADCASTSS Z0 X0 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z0 X0 P2 is 0x48")
step("Verify: VBROADCASTSS Z0 X0 P2 is 0x48")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 0x48
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[3]).to_equal(72)
```

</details>

#### VBROADCASTSS Z0 X0 opcode is 0x18

- VBROADCASTSS Z0 X0 opcode is 0x18
- Verify: VBROADCASTSS Z0 X0 opcode is 0x18
   - Expected: result[4] equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z0 X0 opcode is 0x18")
step("Verify: VBROADCASTSS Z0 X0 opcode is 0x18")
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[4]).to_equal(24)
```

</details>

#### VBROADCASTSS Z0 X0 ModRM is 0xC0

- VBROADCASTSS Z0 X0 ModRM is 0xC0
- Verify: VBROADCASTSS Z0 X0 ModRM is 0xC0
   - Expected: result[5] equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z0 X0 ModRM is 0xC0")
step("Verify: VBROADCASTSS Z0 X0 ModRM is 0xC0")
# ModRM: mod=11 reg=0(zmm0) rm=0(xmm0) = 0xC0
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VBROADCASTSS zmm31 from xmm0 — dest=31 boundary

#### VBROADCASTSS Z31 X0 P0 is 0x62

- VBROADCASTSS Z31 X0 P0 is 0x62
- Verify: VBROADCASTSS Z31 X0 P0 is 0x62
   - Expected: result[1] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z31 X0 P0 is 0x62")
step("Verify: VBROADCASTSS Z31 X0 P0 is 0x62")
# P0: ~R=0(dest[3]=1) ~X=1 ~B=1 ~R'=0(dest[4]=1) mm=010 = 0x62
val result = emit_avx512_vbroadcastss_zmm_from_xmm(79, 0)
expect(result[1]).to_equal(98)
```

</details>

#### VBROADCASTSS Z31 X0 ModRM is 0xF8

- VBROADCASTSS Z31 X0 ModRM is 0xF8
- Verify: VBROADCASTSS Z31 X0 ModRM is 0xF8
   - Expected: result[5] equals `248`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VBROADCASTSS Z31 X0 ModRM is 0xF8")
step("Verify: VBROADCASTSS Z31 X0 ModRM is 0xF8")
# ModRM: mod=11 reg=7(zmm31%8) rm=0 = 0xF8
val result = emit_avx512_vbroadcastss_zmm_from_xmm(79, 0)
expect(result[5]).to_equal(248)
```

</details>

### AVX-512 emit VSHUFF32X4 zmm0 zmm0 zmm0 0x4E golden

#### VSHUFF32X4 Z0 Z0 Z0 4E emits 7 bytes

- VSHUFF32X4 Z0 Z0 Z0 4E emits 7 bytes
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E emits 7 bytes")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E emits 7 bytes")
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result.len()).to_equal(7)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E escape byte is 0x62

- VSHUFF32X4 Z0 Z0 Z0 4E escape byte is 0x62
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E escape byte is 0x62")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E escape byte is 0x62")
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[0]).to_equal(98)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E P0 is 0xF3

- VSHUFF32X4 Z0 Z0 Z0 4E P0 is 0xF3
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E P0 is 0xF3
   - Expected: result[1] equals `243`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E P0 is 0xF3")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E P0 is 0xF3")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm=011(0F3A) = 0xF3
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[1]).to_equal(243)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E P1 is 0x7D

- VSHUFF32X4 Z0 Z0 Z0 4E P1 is 0x7D
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E P1 is 0x7D
   - Expected: result[2] equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E P1 is 0x7D")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E P1 is 0x7D")
# P1: W=0 ~vvvv=1111 must-1 pp=01(0x66) = 0x7D
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[2]).to_equal(125)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E P2 is 0x48

- VSHUFF32X4 Z0 Z0 Z0 4E P2 is 0x48
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E P2 is 0x48")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E P2 is 0x48")
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[3]).to_equal(72)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E opcode is 0x23

- VSHUFF32X4 Z0 Z0 Z0 4E opcode is 0x23
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E opcode is 0x23
   - Expected: result[4] equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E opcode is 0x23")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E opcode is 0x23")
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[4]).to_equal(35)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E ModRM is 0xC0

- VSHUFF32X4 Z0 Z0 Z0 4E ModRM is 0xC0
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E ModRM is 0xC0
   - Expected: result[5] equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E ModRM is 0xC0")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E ModRM is 0xC0")
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[5]).to_equal(192)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E imm8 is 0x4E

- VSHUFF32X4 Z0 Z0 Z0 4E imm8 is 0x4E
- Verify: VSHUFF32X4 Z0 Z0 Z0 4E imm8 is 0x4E
   - Expected: result[6] equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z0 Z0 Z0 4E imm8 is 0x4E")
step("Verify: VSHUFF32X4 Z0 Z0 Z0 4E imm8 is 0x4E")
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[6]).to_equal(78)
```

</details>

### AVX-512 emit VSHUFF32X4 zmm31 zmm0 zmm0 0x4E — dest=31 boundary

#### VSHUFF32X4 Z31 Z0 Z0 4E P0 is 0x63

- VSHUFF32X4 Z31 Z0 Z0 4E P0 is 0x63
- Verify: VSHUFF32X4 Z31 Z0 Z0 4E P0 is 0x63
   - Expected: result[1] equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z31 Z0 Z0 4E P0 is 0x63")
step("Verify: VSHUFF32X4 Z31 Z0 Z0 4E P0 is 0x63")
# P0: ~R=0(dest[3]=1) ~X=1 ~B=1 ~R'=0(dest[4]=1) mm=011 = 0x63
val result = emit_avx512_vshuff32x4_zmm(79, 48, 48, 0x4E)
expect(result[1]).to_equal(99)
```

</details>

#### VSHUFF32X4 Z31 Z0 Z0 4E ModRM is 0xF8

- VSHUFF32X4 Z31 Z0 Z0 4E ModRM is 0xF8
- Verify: VSHUFF32X4 Z31 Z0 Z0 4E ModRM is 0xF8
   - Expected: result[5] equals `248`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VSHUFF32X4 Z31 Z0 Z0 4E ModRM is 0xF8")
step("Verify: VSHUFF32X4 Z31 Z0 Z0 4E ModRM is 0xF8")
val result = emit_avx512_vshuff32x4_zmm(79, 48, 48, 0x4E)
expect(result[5]).to_equal(248)
```

</details>

### AVX-512 emit VPERMPS zmm0 index=zmm1 src=zmm0 golden

#### VPERMPS Z0 Z1 Z0 emits 6 bytes

- VPERMPS Z0 Z1 Z0 emits 6 bytes
- Verify: VPERMPS Z0 Z1 Z0 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPERMPS Z0 Z1 Z0 emits 6 bytes")
step("Verify: VPERMPS Z0 Z1 Z0 emits 6 bytes")
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result.len()).to_equal(6)
```

</details>

#### VPERMPS Z0 Z1 Z0 P0 is 0xF2

- VPERMPS Z0 Z1 Z0 P0 is 0xF2
- Verify: VPERMPS Z0 Z1 Z0 P0 is 0xF2
   - Expected: result[1] equals `242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPERMPS Z0 Z1 Z0 P0 is 0xF2")
step("Verify: VPERMPS Z0 Z1 Z0 P0 is 0xF2")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 mm=010(0F38) = 0xF2
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[1]).to_equal(242)
```

</details>

#### VPERMPS Z0 Z1 Z0 P1 is 0x75

- VPERMPS Z0 Z1 Z0 P1 is 0x75
- Verify: VPERMPS Z0 Z1 Z0 P1 is 0x75
   - Expected: result[2] equals `117`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPERMPS Z0 Z1 Z0 P1 is 0x75")
step("Verify: VPERMPS Z0 Z1 Z0 P1 is 0x75")
# P1: W=0 ~vvvv=1110(zmm1 idx=1) must-1 pp=01(0x66) = 0x75
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[2]).to_equal(117)
```

</details>

#### VPERMPS Z0 Z1 Z0 opcode is 0x16

- VPERMPS Z0 Z1 Z0 opcode is 0x16
- Verify: VPERMPS Z0 Z1 Z0 opcode is 0x16
   - Expected: result[4] equals `22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPERMPS Z0 Z1 Z0 opcode is 0x16")
step("Verify: VPERMPS Z0 Z1 Z0 opcode is 0x16")
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[4]).to_equal(22)
```

</details>

#### VPERMPS Z0 Z1 Z0 ModRM is 0xC0

- VPERMPS Z0 Z1 Z0 ModRM is 0xC0
- Verify: VPERMPS Z0 Z1 Z0 ModRM is 0xC0
   - Expected: result[5] equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPERMPS Z0 Z1 Z0 ModRM is 0xC0")
step("Verify: VPERMPS Z0 Z1 Z0 ModRM is 0xC0")
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VPERMPS src2=zmm31 — X-bit ZMM16-31 rm extension

#### VPERMPS Z0 Z0 Z31 P0 is 0x92

- VPERMPS Z0 Z0 Z31 P0 is 0x92
- Verify: VPERMPS Z0 Z0 Z31 P0 is 0x92
   - Expected: result[1] equals `146`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPERMPS Z0 Z0 Z31 P0 is 0x92")
step("Verify: VPERMPS Z0 Z0 Z31 P0 is 0x92")
# P0: ~R=1 ~X=0(src2=31→X=1) ~B=0(src2[3]=1) ~R'=1 mm=010 = 0x92
val result = emit_avx512_vpermps_zmm(48, 48, 79)
expect(result[1]).to_equal(146)
```

</details>

#### VPERMPS Z0 Z0 Z31 ModRM is 0xC7

- VPERMPS Z0 Z0 Z31 ModRM is 0xC7
- Verify: VPERMPS Z0 Z0 Z31 ModRM is 0xC7
   - Expected: result[5] equals `199`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPERMPS Z0 Z0 Z31 ModRM is 0xC7")
step("Verify: VPERMPS Z0 Z0 Z31 ModRM is 0xC7")
# ModRM: mod=11 reg=0 rm=7(31%8) = 0xC7
val result = emit_avx512_vpermps_zmm(48, 48, 79)
expect(result[5]).to_equal(199)
```

</details>

### AVX-512 emit VMAXPS zmm0 zmm0 zmm0 canonical golden

#### VMAXPS Z0 Z0 Z0 emits 6 bytes

- VMAXPS Z0 Z0 Z0 emits 6 bytes
- Verify: VMAXPS Z0 Z0 Z0 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z0 emits 6 bytes")
step("Verify: VMAXPS Z0 Z0 Z0 emits 6 bytes")
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result.len()).to_equal(6)
```

</details>

#### VMAXPS Z0 Z0 Z0 P0 is 0xF1

- VMAXPS Z0 Z0 Z0 P0 is 0xF1
- Verify: VMAXPS Z0 Z0 Z0 P0 is 0xF1
   - Expected: result[1] equals `241`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z0 P0 is 0xF1")
step("Verify: VMAXPS Z0 Z0 Z0 P0 is 0xF1")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 mm=001(0F) = 0xF1
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[1]).to_equal(241)
```

</details>

#### VMAXPS Z0 Z0 Z0 P1 is 0x7C

- VMAXPS Z0 Z0 Z0 P1 is 0x7C
- Verify: VMAXPS Z0 Z0 Z0 P1 is 0x7C
   - Expected: result[2] equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z0 P1 is 0x7C")
step("Verify: VMAXPS Z0 Z0 Z0 P1 is 0x7C")
# P1: W=0 ~vvvv=1111 must-1 pp=00(none) = 0x7C
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[2]).to_equal(124)
```

</details>

#### VMAXPS Z0 Z0 Z0 P2 is 0x48

- VMAXPS Z0 Z0 Z0 P2 is 0x48
- Verify: VMAXPS Z0 Z0 Z0 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z0 P2 is 0x48")
step("Verify: VMAXPS Z0 Z0 Z0 P2 is 0x48")
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[3]).to_equal(72)
```

</details>

#### VMAXPS Z0 Z0 Z0 opcode is 0x5F

- VMAXPS Z0 Z0 Z0 opcode is 0x5F
- Verify: VMAXPS Z0 Z0 Z0 opcode is 0x5F
   - Expected: result[4] equals `95`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z0 opcode is 0x5F")
step("Verify: VMAXPS Z0 Z0 Z0 opcode is 0x5F")
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[4]).to_equal(95)
```

</details>

#### VMAXPS Z0 Z0 Z0 ModRM is 0xC0

- VMAXPS Z0 Z0 Z0 ModRM is 0xC0
- Verify: VMAXPS Z0 Z0 Z0 ModRM is 0xC0
   - Expected: result[5] equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z0 ModRM is 0xC0")
step("Verify: VMAXPS Z0 Z0 Z0 ModRM is 0xC0")
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VMAXPS zmm31 dest — Zd=31 boundary

#### VMAXPS Z31 Z0 Z0 P0 is 0x61

- VMAXPS Z31 Z0 Z0 P0 is 0x61
- Verify: VMAXPS Z31 Z0 Z0 P0 is 0x61
   - Expected: result[1] equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z31 Z0 Z0 P0 is 0x61")
step("Verify: VMAXPS Z31 Z0 Z0 P0 is 0x61")
# P0: ~R=0(dest[3]=1) ~X=1 ~B=1 ~R'=0(dest[4]=1) mm=001 = 0x61
val result = emit_avx512_vmaxps_zmm(79, 48, 48)
expect(result[1]).to_equal(97)
```

</details>

#### VMAXPS Z31 Z0 Z0 ModRM is 0xF8

- VMAXPS Z31 Z0 Z0 ModRM is 0xF8
- Verify: VMAXPS Z31 Z0 Z0 ModRM is 0xF8
   - Expected: result[5] equals `248`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z31 Z0 Z0 ModRM is 0xF8")
step("Verify: VMAXPS Z31 Z0 Z0 ModRM is 0xF8")
val result = emit_avx512_vmaxps_zmm(79, 48, 48)
expect(result[5]).to_equal(248)
```

</details>

### AVX-512 emit VMAXPS src2=zmm31 — Zn=31 X-bit boundary

#### VMAXPS Z0 Z0 Z31 P0 is 0x91

- VMAXPS Z0 Z0 Z31 P0 is 0x91
- Verify: VMAXPS Z0 Z0 Z31 P0 is 0x91
   - Expected: result[1] equals `145`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z31 P0 is 0x91")
step("Verify: VMAXPS Z0 Z0 Z31 P0 is 0x91")
# P0: ~R=1 ~X=0(src2=31 X=1) ~B=0(src2[3]=1) ~R'=1 mm=001 = 0x91
val result = emit_avx512_vmaxps_zmm(48, 48, 79)
expect(result[1]).to_equal(145)
```

</details>

#### VMAXPS Z0 Z0 Z31 ModRM is 0xC7

- VMAXPS Z0 Z0 Z31 ModRM is 0xC7
- Verify: VMAXPS Z0 Z0 Z31 ModRM is 0xC7
   - Expected: result[5] equals `199`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z0 Z31 ModRM is 0xC7")
step("Verify: VMAXPS Z0 Z0 Z31 ModRM is 0xC7")
val result = emit_avx512_vmaxps_zmm(48, 48, 79)
expect(result[5]).to_equal(199)
```

</details>

### AVX-512 emit VMINPS zmm0 zmm0 zmm0 canonical golden

#### VMINPS Z0 Z0 Z0 emits 6 bytes

- VMINPS Z0 Z0 Z0 emits 6 bytes
- Verify: VMINPS Z0 Z0 Z0 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z0 Z0 emits 6 bytes")
step("Verify: VMINPS Z0 Z0 Z0 emits 6 bytes")
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result.len()).to_equal(6)
```

</details>

#### VMINPS Z0 Z0 Z0 P0 is 0xF1

- VMINPS Z0 Z0 Z0 P0 is 0xF1
- Verify: VMINPS Z0 Z0 Z0 P0 is 0xF1
   - Expected: result[1] equals `241`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z0 Z0 P0 is 0xF1")
step("Verify: VMINPS Z0 Z0 Z0 P0 is 0xF1")
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[1]).to_equal(241)
```

</details>

#### VMINPS Z0 Z0 Z0 P1 is 0x7C

- VMINPS Z0 Z0 Z0 P1 is 0x7C
- Verify: VMINPS Z0 Z0 Z0 P1 is 0x7C
   - Expected: result[2] equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z0 Z0 P1 is 0x7C")
step("Verify: VMINPS Z0 Z0 Z0 P1 is 0x7C")
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[2]).to_equal(124)
```

</details>

#### VMINPS Z0 Z0 Z0 opcode is 0x5D

- VMINPS Z0 Z0 Z0 opcode is 0x5D
- Verify: VMINPS Z0 Z0 Z0 opcode is 0x5D
   - Expected: result[4] equals `93`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z0 Z0 opcode is 0x5D")
step("Verify: VMINPS Z0 Z0 Z0 opcode is 0x5D")
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[4]).to_equal(93)
```

</details>

#### VMINPS Z0 Z0 Z0 ModRM is 0xC0

- VMINPS Z0 Z0 Z0 ModRM is 0xC0
- Verify: VMINPS Z0 Z0 Z0 ModRM is 0xC0
   - Expected: result[5] equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z0 Z0 ModRM is 0xC0")
step("Verify: VMINPS Z0 Z0 Z0 ModRM is 0xC0")
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VMINPS src1=zmm31 — Zn=31 V-prime boundary

#### VMINPS Z0 Z31 Z0 P1 is 0x04

- VMINPS Z0 Z31 Z0 P1 is 0x04
- Verify: VMINPS Z0 Z31 Z0 P1 is 0x04
   - Expected: result[2] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z31 Z0 P1 is 0x04")
step("Verify: VMINPS Z0 Z31 Z0 P1 is 0x04")
# P1: W=0 ~vvvv=0000(src1=31→vvvv_lo4=15) must-1 pp=00 = 0x04
val result = emit_avx512_vminps_zmm(48, 79, 48)
expect(result[2]).to_equal(4)
```

</details>

#### VMINPS Z0 Z31 Z0 P2 is 0x40

- VMINPS Z0 Z31 Z0 P2 is 0x40
- Verify: VMINPS Z0 Z31 Z0 P2 is 0x40
   - Expected: result[3] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z31 Z0 P2 is 0x40")
step("Verify: VMINPS Z0 Z31 Z0 P2 is 0x40")
# P2: z=0 L'=1 L=0 b=0 ~V'=0(V'=1 for src1=31) aaa=000 = 0x40
val result = emit_avx512_vminps_zmm(48, 79, 48)
expect(result[3]).to_equal(64)
```

</details>

### AVX-512 emit VMAXPS src1=zmm16 — V-prime bit boundary

#### VMAXPS Z0 Z16 Z0 P2 is 0x40

- VMAXPS Z0 Z16 Z0 P2 is 0x40
- Verify: VMAXPS Z0 Z16 Z0 P2 is 0x40
   - Expected: result[3] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z16 Z0 P2 is 0x40")
step("Verify: VMAXPS Z0 Z16 Z0 P2 is 0x40")
# P2: z=0 L'=1 L=0 b=0 ~V'=0(src1=16 V'=1) aaa=000 = 0x40
val result = emit_avx512_vmaxps_zmm(48, 64, 48)
expect(result[3]).to_equal(64)
```

</details>

#### VMAXPS Z0 Z16 Z0 P1 is 0x7C

- VMAXPS Z0 Z16 Z0 P1 is 0x7C
- Verify: VMAXPS Z0 Z16 Z0 P1 is 0x7C
   - Expected: result[2] equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMAXPS Z0 Z16 Z0 P1 is 0x7C")
step("Verify: VMAXPS Z0 Z16 Z0 P1 is 0x7C")
# P1: ~vvvv=1111(src1=16→vvvv_lo4=0→not_vvvv=15) pp=00 = 0x7C
val result = emit_avx512_vmaxps_zmm(48, 64, 48)
expect(result[2]).to_equal(124)
```

</details>

### AVX-512 emit VMINPS src2=zmm16 — X-bit without B-bit boundary

#### VMINPS Z0 Z0 Z16 P0 is 0xB1

- VMINPS Z0 Z0 Z16 P0 is 0xB1
- Verify: VMINPS Z0 Z0 Z16 P0 is 0xB1
   - Expected: result[1] equals `177`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z0 Z16 P0 is 0xB1")
step("Verify: VMINPS Z0 Z0 Z16 P0 is 0xB1")
# P0: ~R=1 ~X=0(src2[4]=1) ~B=1(src2[3]=0) ~R'=1 mm=001 = 0xB1 = 177
val result = emit_avx512_vminps_zmm(48, 48, 64)
expect(result[1]).to_equal(177)
```

</details>

#### VMINPS Z0 Z0 Z16 opcode is 0x5D

- VMINPS Z0 Z0 Z16 opcode is 0x5D
- Verify: VMINPS Z0 Z0 Z16 opcode is 0x5D
   - Expected: result[4] equals `93`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMINPS Z0 Z0 Z16 opcode is 0x5D")
step("Verify: VMINPS Z0 Z0 Z16 opcode is 0x5D")
val result = emit_avx512_vminps_zmm(48, 48, 64)
expect(result[4]).to_equal(93)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-AVX-512-EMIT-VBROADCASTSS-ZMM0-FROM-XMM0-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1af3e09f6da46aa78ed5c5c6cbaddfacb4bf757eebc1210a3adcf1a588950f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1af3e09f6da46aa78ed5c5c6cbaddfacb4bf757eebc1210a3adcf1a588950f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1af3e09f6da46aa78ed5c5c6cbaddfacb4bf757eebc1210a3adcf1a588950f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/avx512_reduction_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/avx512_reduction_emit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/avx512_reduction_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/avx512_reduction_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/avx512_reduction_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 47 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/avx512_reduction_emit_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VBROADCASTSS Z0 X0 emits 6 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_reduction_emit_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VBROADCASTSS Z0 X0 escape byte is 0x62' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_reduction_emit_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VBROADCASTSS Z0 X0 P0 is 0xF2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
