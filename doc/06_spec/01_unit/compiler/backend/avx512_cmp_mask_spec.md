# avx512_cmp_mask_spec

> Purpose: Prove that AVX-512 EVEX emit VPCMPEQD compare-to-mask golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_cmp_mask_spec

Purpose: Prove that AVX-512 EVEX emit VPCMPEQD compare-to-mask golden.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_cmp_mask_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AVX-512 EVEX emit VPCMPEQD compare-to-mask golden.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AVX-512 EVEX emit VPCMPEQD compare-to-mask golden

#### VPCMPEQD k0 zmm0 zmm1 emits 6 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VPCMPEQD k0 zmm0 zmm1 emits 6 bytes
- Verify: VPCMPEQD k0 zmm0 zmm1 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQD k0 zmm0 zmm1 emits 6 bytes")
step("Verify: VPCMPEQD k0 zmm0 zmm1 emits 6 bytes")
# @req: REQ-COMP-AVX-512-EVEX-EMIT-VPCMPEQD-COMPARE-TO-MA-001
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result.len()).to_equal(6)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 escape byte is 0x62

- VPCMPEQD k0 zmm0 zmm1 escape byte is 0x62
- Verify: VPCMPEQD k0 zmm0 zmm1 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQD k0 zmm0 zmm1 escape byte is 0x62")
step("Verify: VPCMPEQD k0 zmm0 zmm1 escape byte is 0x62")
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 P0 is 0xF2

- VPCMPEQD k0 zmm0 zmm1 P0 is 0xF2
- Verify: VPCMPEQD k0 zmm0 zmm1 P0 is 0xF2
   - Expected: result[1] equals `242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQD k0 zmm0 zmm1 P0 is 0xF2")
step("Verify: VPCMPEQD k0 zmm0 zmm1 P0 is 0xF2")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=010 (0F38 map) = 242
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[1]).to_equal(242)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 P1 is 0x7D

- VPCMPEQD k0 zmm0 zmm1 P1 is 0x7D
- Verify: VPCMPEQD k0 zmm0 zmm1 P1 is 0x7D
   - Expected: result[2] equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQD k0 zmm0 zmm1 P1 is 0x7D")
step("Verify: VPCMPEQD k0 zmm0 zmm1 P1 is 0x7D")
# P1: W=0 ~vvvv=1111(src1=zmm0,idx=0) must-1 pp=01(0x66) = 125
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[2]).to_equal(125)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 P2 is 0x48

- VPCMPEQD k0 zmm0 zmm1 P2 is 0x48
- Verify: VPCMPEQD k0 zmm0 zmm1 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQD k0 zmm0 zmm1 P2 is 0x48")
step("Verify: VPCMPEQD k0 zmm0 zmm1 P2 is 0x48")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 72
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 opcode is 0x76

- VPCMPEQD k0 zmm0 zmm1 opcode is 0x76
- Verify: VPCMPEQD k0 zmm0 zmm1 opcode is 0x76
   - Expected: result[4] equals `118`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQD k0 zmm0 zmm1 opcode is 0x76")
step("Verify: VPCMPEQD k0 zmm0 zmm1 opcode is 0x76")
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[4]).to_equal(118)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 ModRM is 0xC1

- VPCMPEQD k0 zmm0 zmm1 ModRM is 0xC1
- Verify: VPCMPEQD k0 zmm0 zmm1 ModRM is 0xC1
   - Expected: result[5] equals `193`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQD k0 zmm0 zmm1 ModRM is 0xC1")
step("Verify: VPCMPEQD k0 zmm0 zmm1 ModRM is 0xC1")
# ModRM: mod=11 reg=0(k0) rm=1(zmm1) = 192+0+1 = 193
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[5]).to_equal(193)
```

</details>

### AVX-512 EVEX emit VPCMPEQQ compare-to-mask golden

#### VPCMPEQQ k1 zmm0 zmm1 emits 6 bytes

- VPCMPEQQ k1 zmm0 zmm1 emits 6 bytes
- Verify: VPCMPEQQ k1 zmm0 zmm1 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ k1 zmm0 zmm1 emits 6 bytes")
step("Verify: VPCMPEQQ k1 zmm0 zmm1 emits 6 bytes")
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result.len()).to_equal(6)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 escape byte is 0x62

- VPCMPEQQ k1 zmm0 zmm1 escape byte is 0x62
- Verify: VPCMPEQQ k1 zmm0 zmm1 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ k1 zmm0 zmm1 escape byte is 0x62")
step("Verify: VPCMPEQQ k1 zmm0 zmm1 escape byte is 0x62")
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 P0 is 0xF2

- VPCMPEQQ k1 zmm0 zmm1 P0 is 0xF2
- Verify: VPCMPEQQ k1 zmm0 zmm1 P0 is 0xF2
   - Expected: result[1] equals `242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ k1 zmm0 zmm1 P0 is 0xF2")
step("Verify: VPCMPEQQ k1 zmm0 zmm1 P0 is 0xF2")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=010 (0F38 map) = 242
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[1]).to_equal(242)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 P1 is 0xFD

- VPCMPEQQ k1 zmm0 zmm1 P1 is 0xFD
- Verify: VPCMPEQQ k1 zmm0 zmm1 P1 is 0xFD
   - Expected: result[2] equals `253`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ k1 zmm0 zmm1 P1 is 0xFD")
step("Verify: VPCMPEQQ k1 zmm0 zmm1 P1 is 0xFD")
# P1: W=1 ~vvvv=1111 must-1 pp=01(0x66) = 253 (W=1 differentiates Q from D)
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[2]).to_equal(253)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 P2 is 0x48

- VPCMPEQQ k1 zmm0 zmm1 P2 is 0x48
- Verify: VPCMPEQQ k1 zmm0 zmm1 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ k1 zmm0 zmm1 P2 is 0x48")
step("Verify: VPCMPEQQ k1 zmm0 zmm1 P2 is 0x48")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 72
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 opcode is 0x29

- VPCMPEQQ k1 zmm0 zmm1 opcode is 0x29
- Verify: VPCMPEQQ k1 zmm0 zmm1 opcode is 0x29
   - Expected: result[4] equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ k1 zmm0 zmm1 opcode is 0x29")
step("Verify: VPCMPEQQ k1 zmm0 zmm1 opcode is 0x29")
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[4]).to_equal(41)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 ModRM is 0xC9

- VPCMPEQQ k1 zmm0 zmm1 ModRM is 0xC9
- Verify: VPCMPEQQ k1 zmm0 zmm1 ModRM is 0xC9
   - Expected: result[5] equals `201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ k1 zmm0 zmm1 ModRM is 0xC9")
step("Verify: VPCMPEQQ k1 zmm0 zmm1 ModRM is 0xC9")
# ModRM: mod=11 reg=1(k1) rm=1(zmm1) = 192+8+1 = 201
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[5]).to_equal(201)
```

</details>

#### VPCMPEQQ P1 byte differs from VPCMPEQD P1 by W-bit (0x7D vs 0xFD)

- VPCMPEQQ P1 byte differs from VPCMPEQD P1 by W-bit (0x7D vs 0xFD)
- Verify: VPCMPEQQ P1 byte differs from VPCMPEQD P1 by W-bit (0x7D vs 0xFD)
   - Expected: rd[2] equals `125`
   - Expected: rq[2] equals `253`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPEQQ P1 byte differs from VPCMPEQD P1 by W-bit (0x7D vs 0xFD)")
step("Verify: VPCMPEQQ P1 byte differs from VPCMPEQD P1 by W-bit (0x7D vs 0xFD)")
# W=0 → P1=0x7D=125 for D-form; W=1 → P1=0xFD=253 for Q-form
val rd = emit_avx512_vpcmpeqd(0, 48, 49)
val rq = emit_avx512_vpcmpeqq(1, 48, 49)
expect(rd[2]).to_equal(125)
expect(rq[2]).to_equal(253)
```

</details>

### AVX-512 EVEX emit VPCMPD imm8-predicate golden

#### VPCMPD k0 zmm0 zmm1 EQ=0 emits 7 bytes

- VPCMPD k0 zmm0 zmm1 EQ=0 emits 7 bytes
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 emits 7 bytes")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 emits 7 bytes")
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 escape byte is 0x62

- VPCMPD k0 zmm0 zmm1 EQ=0 escape byte is 0x62
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 escape byte is 0x62")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 escape byte is 0x62")
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 P0 is 0xF3

- VPCMPD k0 zmm0 zmm1 EQ=0 P0 is 0xF3
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 P0 is 0xF3
   - Expected: result[1] equals `243`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 P0 is 0xF3")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 P0 is 0xF3")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=011 (0F3A map) = 243
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[1]).to_equal(243)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 P1 is 0x7D

- VPCMPD k0 zmm0 zmm1 EQ=0 P1 is 0x7D
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 P1 is 0x7D
   - Expected: result[2] equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 P1 is 0x7D")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 P1 is 0x7D")
# P1: W=0 ~vvvv=1111 must-1 pp=01(0x66) = 125
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[2]).to_equal(125)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 P2 is 0x48

- VPCMPD k0 zmm0 zmm1 EQ=0 P2 is 0x48
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 P2 is 0x48")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 P2 is 0x48")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 72
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 opcode is 0x1F

- VPCMPD k0 zmm0 zmm1 EQ=0 opcode is 0x1F
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 opcode is 0x1F
   - Expected: result[4] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 opcode is 0x1F")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 opcode is 0x1F")
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[4]).to_equal(31)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 ModRM is 0xC1

- VPCMPD k0 zmm0 zmm1 EQ=0 ModRM is 0xC1
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 ModRM is 0xC1
   - Expected: result[5] equals `193`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 ModRM is 0xC1")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 ModRM is 0xC1")
# ModRM: mod=11 reg=0(k0) rm=1(zmm1) = 193
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[5]).to_equal(193)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 imm8 is 0x00

- VPCMPD k0 zmm0 zmm1 EQ=0 imm8 is 0x00
- Verify: VPCMPD k0 zmm0 zmm1 EQ=0 imm8 is 0x00
   - Expected: result[6] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 EQ=0 imm8 is 0x00")
step("Verify: VPCMPD k0 zmm0 zmm1 EQ=0 imm8 is 0x00")
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[6]).to_equal(0)
```

</details>

#### VPCMPD k0 zmm0 zmm1 LT=1 emits 7 bytes

- VPCMPD k0 zmm0 zmm1 LT=1 emits 7 bytes
- Verify: VPCMPD k0 zmm0 zmm1 LT=1 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 LT=1 emits 7 bytes")
step("Verify: VPCMPD k0 zmm0 zmm1 LT=1 emits 7 bytes")
val result = emit_avx512_vpcmpd(0, 48, 49, 1)
expect(result.len()).to_equal(7)
```

</details>

#### VPCMPD k0 zmm0 zmm1 LT=1 imm8 is 0x01

- VPCMPD k0 zmm0 zmm1 LT=1 imm8 is 0x01
- Verify: VPCMPD k0 zmm0 zmm1 LT=1 imm8 is 0x01
   - Expected: result[6] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD k0 zmm0 zmm1 LT=1 imm8 is 0x01")
step("Verify: VPCMPD k0 zmm0 zmm1 LT=1 imm8 is 0x01")
val result = emit_avx512_vpcmpd(0, 48, 49, 1)
expect(result[6]).to_equal(1)
```

</details>

#### VPCMPD LT differs from EQ only in imm8 byte

- VPCMPD LT differs from EQ only in imm8 byte
- Verify: VPCMPD LT differs from EQ only in imm8 byte
   - Expected: req[0] equals `rlt[0]`
   - Expected: req[1] equals `rlt[1]`
   - Expected: req[2] equals `rlt[2]`
   - Expected: req[3] equals `rlt[3]`
   - Expected: req[4] equals `rlt[4]`
   - Expected: req[5] equals `rlt[5]`
   - Expected: req[6] equals `0`
   - Expected: rlt[6] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPD LT differs from EQ only in imm8 byte")
step("Verify: VPCMPD LT differs from EQ only in imm8 byte")
# All prefix bytes identical; only imm8 differs
val req = emit_avx512_vpcmpd(0, 48, 49, 0)
val rlt = emit_avx512_vpcmpd(0, 48, 49, 1)
expect(req[0]).to_equal(rlt[0])
expect(req[1]).to_equal(rlt[1])
expect(req[2]).to_equal(rlt[2])
expect(req[3]).to_equal(rlt[3])
expect(req[4]).to_equal(rlt[4])
expect(req[5]).to_equal(rlt[5])
expect(req[6]).to_equal(0)
expect(rlt[6]).to_equal(1)
```

</details>

### AVX-512 EVEX emit VPCMPQ imm8-predicate golden

#### VPCMPQ k1 zmm0 zmm1 EQ=0 emits 7 bytes

- VPCMPQ k1 zmm0 zmm1 EQ=0 emits 7 bytes
- Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 emits 7 bytes
   - Expected: result.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ k1 zmm0 zmm1 EQ=0 emits 7 bytes")
step("Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 emits 7 bytes")
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 P0 is 0xF3

- VPCMPQ k1 zmm0 zmm1 EQ=0 P0 is 0xF3
- Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 P0 is 0xF3
   - Expected: result[1] equals `243`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ k1 zmm0 zmm1 EQ=0 P0 is 0xF3")
step("Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 P0 is 0xF3")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=011 (0F3A map) = 243
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[1]).to_equal(243)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 P1 is 0xFD

- VPCMPQ k1 zmm0 zmm1 EQ=0 P1 is 0xFD
- Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 P1 is 0xFD
   - Expected: result[2] equals `253`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ k1 zmm0 zmm1 EQ=0 P1 is 0xFD")
step("Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 P1 is 0xFD")
# P1: W=1 ~vvvv=1111 must-1 pp=01(0x66) = 253
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[2]).to_equal(253)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 P2 is 0x48

- VPCMPQ k1 zmm0 zmm1 EQ=0 P2 is 0x48
- Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ k1 zmm0 zmm1 EQ=0 P2 is 0x48")
step("Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 P2 is 0x48")
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 opcode is 0x1F

- VPCMPQ k1 zmm0 zmm1 EQ=0 opcode is 0x1F
- Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 opcode is 0x1F
   - Expected: result[4] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ k1 zmm0 zmm1 EQ=0 opcode is 0x1F")
step("Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 opcode is 0x1F")
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[4]).to_equal(31)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 ModRM is 0xC9

- VPCMPQ k1 zmm0 zmm1 EQ=0 ModRM is 0xC9
- Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 ModRM is 0xC9
   - Expected: result[5] equals `201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ k1 zmm0 zmm1 EQ=0 ModRM is 0xC9")
step("Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 ModRM is 0xC9")
# ModRM: mod=11 reg=1(k1) rm=1(zmm1) = 201
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[5]).to_equal(201)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 imm8 is 0x00

- VPCMPQ k1 zmm0 zmm1 EQ=0 imm8 is 0x00
- Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 imm8 is 0x00
   - Expected: result[6] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ k1 zmm0 zmm1 EQ=0 imm8 is 0x00")
step("Verify: VPCMPQ k1 zmm0 zmm1 EQ=0 imm8 is 0x00")
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[6]).to_equal(0)
```

</details>

#### VPCMPQ P1 byte differs from VPCMPD P1 by W-bit (0x7D vs 0xFD)

- VPCMPQ P1 byte differs from VPCMPD P1 by W-bit (0x7D vs 0xFD)
- Verify: VPCMPQ P1 byte differs from VPCMPD P1 by W-bit (0x7D vs 0xFD)
   - Expected: rd[2] equals `125`
   - Expected: rq[2] equals `253`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("VPCMPQ P1 byte differs from VPCMPD P1 by W-bit (0x7D vs 0xFD)")
step("Verify: VPCMPQ P1 byte differs from VPCMPD P1 by W-bit (0x7D vs 0xFD)")
# Same opcode 0x1F; W=0→P1=125 for D-form, W=1→P1=253 for Q-form
val rd = emit_avx512_vpcmpd(0, 48, 49, 0)
val rq = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(rd[2]).to_equal(125)
expect(rq[2]).to_equal(253)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-AVX-512-EVEX-EMIT-VPCMPEQD-COMPARE-TO-MA-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4dd1708ca397a58afb56ea3ae6e217db3e1bec8a8553739c97afb6b7e58675e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4dd1708ca397a58afb56ea3ae6e217db3e1bec8a8553739c97afb6b7e58675e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4dd1708ca397a58afb56ea3ae6e217db3e1bec8a8553739c97afb6b7e58675e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/avx512_cmp_mask_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/avx512_cmp_mask_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/avx512_cmp_mask_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/avx512_cmp_mask_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/avx512_cmp_mask_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 37 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/avx512_cmp_mask_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPCMPEQD k0 zmm0 zmm1 emits 6 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/avx512_cmp_mask_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPCMPEQD k0 zmm0 zmm1 escape byte is 0x62' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/avx512_cmp_mask_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPCMPEQD k0 zmm0 zmm1 P0 is 0xF2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
