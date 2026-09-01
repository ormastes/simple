# avx512_mask_emit_spec

> Purpose: Prove that AVX-512 EVEX emit VPCMPEQD zmm-to-k golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_mask_emit_spec

Purpose: Prove that AVX-512 EVEX emit VPCMPEQD zmm-to-k golden.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/avx512_mask_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AVX-512 EVEX emit VPCMPEQD zmm-to-k golden.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AVX-512 EVEX emit VPCMPEQD zmm-to-k golden

#### VPCMPEQD k1 zmm0 zmm0 emits 6 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VPCMPEQD k1 zmm0 zmm0 emits 6 bytes
- Verify: VPCMPEQD k1 zmm0 zmm0 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPCMPEQD k1 zmm0 zmm0 emits 6 bytes")
step("Verify: VPCMPEQD k1 zmm0 zmm0 emits 6 bytes")
# @req: REQ-COMP-AVX-512-EVEX-EMIT-VPCMPEQD-ZMM-TO-K-GOLD-001
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result.len()).to_equal(6)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 escape byte is 0x62

- VPCMPEQD k1 zmm0 zmm0 escape byte is 0x62
- Verify: VPCMPEQD k1 zmm0 zmm0 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPCMPEQD k1 zmm0 zmm0 escape byte is 0x62")
step("Verify: VPCMPEQD k1 zmm0 zmm0 escape byte is 0x62")
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 P0 is 0xF1

- VPCMPEQD k1 zmm0 zmm0 P0 is 0xF1
- Verify: VPCMPEQD k1 zmm0 zmm0 P0 is 0xF1
   - Expected: result[1] equals `241`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPCMPEQD k1 zmm0 zmm0 P0 is 0xF1")
step("Verify: VPCMPEQD k1 zmm0 zmm0 P0 is 0xF1")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 m2=0 m1=0 m0=1 = 0xF1 (mm=001=0F map)
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[1]).to_equal(241)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 P1 is 0x7D

- VPCMPEQD k1 zmm0 zmm0 P1 is 0x7D
- Verify: VPCMPEQD k1 zmm0 zmm0 P1 is 0x7D
   - Expected: result[2] equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPCMPEQD k1 zmm0 zmm0 P1 is 0x7D")
step("Verify: VPCMPEQD k1 zmm0 zmm0 P1 is 0x7D")
# P1: W=0 ~vvvv=1111(zmm0) must-1 pp=01(0x66) = 0x7D
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[2]).to_equal(125)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 P2 is 0x48

- VPCMPEQD k1 zmm0 zmm0 P2 is 0x48
- Verify: VPCMPEQD k1 zmm0 zmm0 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPCMPEQD k1 zmm0 zmm0 P2 is 0x48")
step("Verify: VPCMPEQD k1 zmm0 zmm0 P2 is 0x48")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 0x48
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 opcode is 0x76

- VPCMPEQD k1 zmm0 zmm0 opcode is 0x76
- Verify: VPCMPEQD k1 zmm0 zmm0 opcode is 0x76
   - Expected: result[4] equals `118`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPCMPEQD k1 zmm0 zmm0 opcode is 0x76")
step("Verify: VPCMPEQD k1 zmm0 zmm0 opcode is 0x76")
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[4]).to_equal(118)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 ModRM is 0xC8

- VPCMPEQD k1 zmm0 zmm0 ModRM is 0xC8
- Verify: VPCMPEQD k1 zmm0 zmm0 ModRM is 0xC8
   - Expected: result[5] equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VPCMPEQD k1 zmm0 zmm0 ModRM is 0xC8")
step("Verify: VPCMPEQD k1 zmm0 zmm0 ModRM is 0xC8")
# ModRM: mod=11 reg=1(k1) rm=0(zmm0) = 0xC8
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[5]).to_equal(200)
```

</details>

### AVX-512 VEX emit KANDB k-reg 3-op golden

#### KANDB k1 k2 k3 emits 4 bytes

- KANDB k1 k2 k3 emits 4 bytes
- Verify: KANDB k1 k2 k3 emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDB k1 k2 k3 emits 4 bytes")
step("Verify: KANDB k1 k2 k3 emits 4 bytes")
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KANDB k1 k2 k3 VEX escape is 0xC5

- KANDB k1 k2 k3 VEX escape is 0xC5
- Verify: KANDB k1 k2 k3 VEX escape is 0xC5
   - Expected: result[0] equals `197`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDB k1 k2 k3 VEX escape is 0xC5")
step("Verify: KANDB k1 k2 k3 VEX escape is 0xC5")
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[0]).to_equal(197)
```

</details>

#### KANDB k1 k2 k3 byte1 is 0xED

- KANDB k1 k2 k3 byte1 is 0xED
- Verify: KANDB k1 k2 k3 byte1 is 0xED
   - Expected: result[1] equals `237`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDB k1 k2 k3 byte1 is 0xED")
step("Verify: KANDB k1 k2 k3 byte1 is 0xED")
# byte1: ~R=1 ~vvvv=1101(k2) L=1 pp=01(66) = 0xED
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KANDB k1 k2 k3 opcode is 0x41

- KANDB k1 k2 k3 opcode is 0x41
- Verify: KANDB k1 k2 k3 opcode is 0x41
   - Expected: result[2] equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDB k1 k2 k3 opcode is 0x41")
step("Verify: KANDB k1 k2 k3 opcode is 0x41")
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(65)
```

</details>

#### KANDB k1 k2 k3 ModRM is 0xCB

- KANDB k1 k2 k3 ModRM is 0xCB
- Verify: KANDB k1 k2 k3 ModRM is 0xCB
   - Expected: result[3] equals `203`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDB k1 k2 k3 ModRM is 0xCB")
step("Verify: KANDB k1 k2 k3 ModRM is 0xCB")
# ModRM: mod=11 reg=1(k1) rm=3(k3) = 0xCB
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KORB k-reg 3-op golden

#### KORB k1 k2 k3 emits 4 bytes

- KORB k1 k2 k3 emits 4 bytes
- Verify: KORB k1 k2 k3 emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KORB k1 k2 k3 emits 4 bytes")
step("Verify: KORB k1 k2 k3 emits 4 bytes")
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KORB k1 k2 k3 byte1 is 0xED

- KORB k1 k2 k3 byte1 is 0xED
- Verify: KORB k1 k2 k3 byte1 is 0xED
   - Expected: result[1] equals `237`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KORB k1 k2 k3 byte1 is 0xED")
step("Verify: KORB k1 k2 k3 byte1 is 0xED")
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KORB k1 k2 k3 opcode is 0x45

- KORB k1 k2 k3 opcode is 0x45
- Verify: KORB k1 k2 k3 opcode is 0x45
   - Expected: result[2] equals `69`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KORB k1 k2 k3 opcode is 0x45")
step("Verify: KORB k1 k2 k3 opcode is 0x45")
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(69)
```

</details>

#### KORB k1 k2 k3 ModRM is 0xCB

- KORB k1 k2 k3 ModRM is 0xCB
- Verify: KORB k1 k2 k3 ModRM is 0xCB
   - Expected: result[3] equals `203`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KORB k1 k2 k3 ModRM is 0xCB")
step("Verify: KORB k1 k2 k3 ModRM is 0xCB")
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KXORB k-reg 3-op golden

#### KXORB k1 k2 k3 emits 4 bytes

- KXORB k1 k2 k3 emits 4 bytes
- Verify: KXORB k1 k2 k3 emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KXORB k1 k2 k3 emits 4 bytes")
step("Verify: KXORB k1 k2 k3 emits 4 bytes")
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KXORB k1 k2 k3 byte1 is 0xED

- KXORB k1 k2 k3 byte1 is 0xED
- Verify: KXORB k1 k2 k3 byte1 is 0xED
   - Expected: result[1] equals `237`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KXORB k1 k2 k3 byte1 is 0xED")
step("Verify: KXORB k1 k2 k3 byte1 is 0xED")
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KXORB k1 k2 k3 opcode is 0x47

- KXORB k1 k2 k3 opcode is 0x47
- Verify: KXORB k1 k2 k3 opcode is 0x47
   - Expected: result[2] equals `71`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KXORB k1 k2 k3 opcode is 0x47")
step("Verify: KXORB k1 k2 k3 opcode is 0x47")
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(71)
```

</details>

#### KXORB k1 k2 k3 ModRM is 0xCB

- KXORB k1 k2 k3 ModRM is 0xCB
- Verify: KXORB k1 k2 k3 ModRM is 0xCB
   - Expected: result[3] equals `203`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KXORB k1 k2 k3 ModRM is 0xCB")
step("Verify: KXORB k1 k2 k3 ModRM is 0xCB")
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KANDNB k-reg 3-op golden

#### KANDNB k1 k2 k3 emits 4 bytes

- KANDNB k1 k2 k3 emits 4 bytes
- Verify: KANDNB k1 k2 k3 emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDNB k1 k2 k3 emits 4 bytes")
step("Verify: KANDNB k1 k2 k3 emits 4 bytes")
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KANDNB k1 k2 k3 byte1 is 0xED

- KANDNB k1 k2 k3 byte1 is 0xED
- Verify: KANDNB k1 k2 k3 byte1 is 0xED
   - Expected: result[1] equals `237`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDNB k1 k2 k3 byte1 is 0xED")
step("Verify: KANDNB k1 k2 k3 byte1 is 0xED")
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KANDNB k1 k2 k3 opcode is 0x42

- KANDNB k1 k2 k3 opcode is 0x42
- Verify: KANDNB k1 k2 k3 opcode is 0x42
   - Expected: result[2] equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDNB k1 k2 k3 opcode is 0x42")
step("Verify: KANDNB k1 k2 k3 opcode is 0x42")
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(66)
```

</details>

#### KANDNB k1 k2 k3 ModRM is 0xCB

- KANDNB k1 k2 k3 ModRM is 0xCB
- Verify: KANDNB k1 k2 k3 ModRM is 0xCB
   - Expected: result[3] equals `203`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KANDNB k1 k2 k3 ModRM is 0xCB")
step("Verify: KANDNB k1 k2 k3 ModRM is 0xCB")
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KMOVW gpr-to-k golden

#### KMOVW k1 eax emits 4 bytes

- KMOVW k1 eax emits 4 bytes
- Verify: KMOVW k1 eax emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KMOVW k1 eax emits 4 bytes")
step("Verify: KMOVW k1 eax emits 4 bytes")
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result.len()).to_equal(4)
```

</details>

#### KMOVW k1 eax VEX escape is 0xC5

- KMOVW k1 eax VEX escape is 0xC5
- Verify: KMOVW k1 eax VEX escape is 0xC5
   - Expected: result[0] equals `197`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KMOVW k1 eax VEX escape is 0xC5")
step("Verify: KMOVW k1 eax VEX escape is 0xC5")
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[0]).to_equal(197)
```

</details>

#### KMOVW k1 eax byte1 is 0xF8

- KMOVW k1 eax byte1 is 0xF8
- Verify: KMOVW k1 eax byte1 is 0xF8
   - Expected: result[1] equals `248`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KMOVW k1 eax byte1 is 0xF8")
step("Verify: KMOVW k1 eax byte1 is 0xF8")
# byte1: ~R=1 ~vvvv=1111(unused) L=0 pp=00 = 0xF8
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[1]).to_equal(248)
```

</details>

#### KMOVW k1 eax opcode is 0x92

- KMOVW k1 eax opcode is 0x92
- Verify: KMOVW k1 eax opcode is 0x92
   - Expected: result[2] equals `146`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KMOVW k1 eax opcode is 0x92")
step("Verify: KMOVW k1 eax opcode is 0x92")
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[2]).to_equal(146)
```

</details>

#### KMOVW k1 eax ModRM is 0xC8

- KMOVW k1 eax ModRM is 0xC8
- Verify: KMOVW k1 eax ModRM is 0xC8
   - Expected: result[3] equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("KMOVW k1 eax ModRM is 0xC8")
step("Verify: KMOVW k1 eax ModRM is 0xC8")
# ModRM: mod=11 reg=1(k1) rm=0(eax) = 0xC8
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[3]).to_equal(200)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-AVX-512-EVEX-EMIT-VPCMPEQD-ZMM-TO-K-GOLD-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c693ff2486cd6115cb6e5c66dbb3a5328e5c92ce8d4564699549e1dcbc19a447`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c693ff2486cd6115cb6e5c66dbb3a5328e5c92ce8d4564699549e1dcbc19a447`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c693ff2486cd6115cb6e5c66dbb3a5328e5c92ce8d4564699549e1dcbc19a447`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/avx512_mask_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/avx512_mask_emit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/avx512_mask_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/avx512_mask_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/avx512_mask_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 29 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/avx512_mask_emit_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPCMPEQD k1 zmm0 zmm0 emits 6 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_mask_emit_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPCMPEQD k1 zmm0 zmm0 escape byte is 0x62' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_mask_emit_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VPCMPEQD k1 zmm0 zmm0 P0 is 0xF1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
