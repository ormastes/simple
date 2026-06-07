# Avx512 Cmp Mask Specification

> <details>

<!-- sdn-diagram:id=avx512_cmp_mask_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_cmp_mask_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_cmp_mask_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_cmp_mask_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx512 Cmp Mask Specification

## Scenarios

### AVX-512 EVEX emit VPCMPEQD compare-to-mask golden

#### VPCMPEQD k0 zmm0 zmm1 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result.len()).to_equal(6)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 P0 is 0xF2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=010 (0F38 map) = 242
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[1]).to_equal(242)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 P1 is 0x7D

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111(src1=zmm0,idx=0) must-1 pp=01(0x66) = 125
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[2]).to_equal(125)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 72
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 opcode is 0x76

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[4]).to_equal(118)
```

</details>

#### VPCMPEQD k0 zmm0 zmm1 ModRM is 0xC1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=0(k0) rm=1(zmm1) = 192+0+1 = 193
val result = emit_avx512_vpcmpeqd(0, 48, 49)
expect(result[5]).to_equal(193)
```

</details>

### AVX-512 EVEX emit VPCMPEQQ compare-to-mask golden

#### VPCMPEQQ k1 zmm0 zmm1 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result.len()).to_equal(6)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 P0 is 0xF2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=010 (0F38 map) = 242
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[1]).to_equal(242)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 P1 is 0xFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=1 ~vvvv=1111 must-1 pp=01(0x66) = 253 (W=1 differentiates Q from D)
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[2]).to_equal(253)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 72
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 opcode is 0x29

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[4]).to_equal(41)
```

</details>

#### VPCMPEQQ k1 zmm0 zmm1 ModRM is 0xC9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=1(k1) rm=1(zmm1) = 192+8+1 = 201
val result = emit_avx512_vpcmpeqq(1, 48, 49)
expect(result[5]).to_equal(201)
```

</details>

#### VPCMPEQQ P1 byte differs from VPCMPEQD P1 by W-bit (0x7D vs 0xFD)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# W=0 → P1=0x7D=125 for D-form; W=1 → P1=0xFD=253 for Q-form
val rd = emit_avx512_vpcmpeqd(0, 48, 49)
val rq = emit_avx512_vpcmpeqq(1, 48, 49)
expect(rd[2]).to_equal(125)
expect(rq[2]).to_equal(253)
```

</details>

### AVX-512 EVEX emit VPCMPD imm8-predicate golden

#### VPCMPD k0 zmm0 zmm1 EQ=0 emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 P0 is 0xF3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=011 (0F3A map) = 243
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[1]).to_equal(243)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 P1 is 0x7D

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111 must-1 pp=01(0x66) = 125
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[2]).to_equal(125)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 72
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 opcode is 0x1F

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[4]).to_equal(31)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 ModRM is 0xC1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=0(k0) rm=1(zmm1) = 193
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[5]).to_equal(193)
```

</details>

#### VPCMPD k0 zmm0 zmm1 EQ=0 imm8 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpd(0, 48, 49, 0)
expect(result[6]).to_equal(0)
```

</details>

#### VPCMPD k0 zmm0 zmm1 LT=1 emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpd(0, 48, 49, 1)
expect(result.len()).to_equal(7)
```

</details>

#### VPCMPD k0 zmm0 zmm1 LT=1 imm8 is 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpd(0, 48, 49, 1)
expect(result[6]).to_equal(1)
```

</details>

#### VPCMPD LT differs from EQ only in imm8 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 P0 is 0xF3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm[2:0]=011 (0F3A map) = 243
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[1]).to_equal(243)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 P1 is 0xFD

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=1 ~vvvv=1111 must-1 pp=01(0x66) = 253
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[2]).to_equal(253)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 opcode is 0x1F

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[4]).to_equal(31)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 ModRM is 0xC9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=1(k1) rm=1(zmm1) = 201
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[5]).to_equal(201)
```

</details>

#### VPCMPQ k1 zmm0 zmm1 EQ=0 imm8 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(result[6]).to_equal(0)
```

</details>

#### VPCMPQ P1 byte differs from VPCMPD P1 by W-bit (0x7D vs 0xFD)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same opcode 0x1F; W=0→P1=125 for D-form, W=1→P1=253 for Q-form
val rd = emit_avx512_vpcmpd(0, 48, 49, 0)
val rq = emit_avx512_vpcmpq(1, 48, 49, 0)
expect(rd[2]).to_equal(125)
expect(rq[2]).to_equal(253)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_cmp_mask_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX-512 EVEX emit VPCMPEQD compare-to-mask golden
- AVX-512 EVEX emit VPCMPEQQ compare-to-mask golden
- AVX-512 EVEX emit VPCMPD imm8-predicate golden
- AVX-512 EVEX emit VPCMPQ imm8-predicate golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
