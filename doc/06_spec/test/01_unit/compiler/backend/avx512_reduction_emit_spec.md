# Avx512 Reduction Emit Specification

> <details>

<!-- sdn-diagram:id=avx512_reduction_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_reduction_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_reduction_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_reduction_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx512 Reduction Emit Specification

## Scenarios

### AVX-512 emit VBROADCASTSS zmm0 from xmm0 golden

#### VBROADCASTSS Z0 X0 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result.len()).to_equal(6)
```

</details>

#### VBROADCASTSS Z0 X0 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[0]).to_equal(98)
```

</details>

#### VBROADCASTSS Z0 X0 P0 is 0xF2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm=010(0F38) = 0xF2
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[1]).to_equal(242)
```

</details>

#### VBROADCASTSS Z0 X0 P1 is 0x7D

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111(unused) must-1 pp=01(0x66) = 0x7D
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[2]).to_equal(125)
```

</details>

#### VBROADCASTSS Z0 X0 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 0x48
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[3]).to_equal(72)
```

</details>

#### VBROADCASTSS Z0 X0 opcode is 0x18

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[4]).to_equal(24)
```

</details>

#### VBROADCASTSS Z0 X0 ModRM is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=0(zmm0) rm=0(xmm0) = 0xC0
val result = emit_avx512_vbroadcastss_zmm_from_xmm(48, 0)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VBROADCASTSS zmm31 from xmm0 — dest=31 boundary

#### VBROADCASTSS Z31 X0 P0 is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=0(dest[3]=1) ~X=1 ~B=1 ~R'=0(dest[4]=1) mm=010 = 0x62
val result = emit_avx512_vbroadcastss_zmm_from_xmm(79, 0)
expect(result[1]).to_equal(98)
```

</details>

#### VBROADCASTSS Z31 X0 ModRM is 0xF8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=7(zmm31%8) rm=0 = 0xF8
val result = emit_avx512_vbroadcastss_zmm_from_xmm(79, 0)
expect(result[5]).to_equal(248)
```

</details>

### AVX-512 emit VSHUFF32X4 zmm0 zmm0 zmm0 0x4E golden

#### VSHUFF32X4 Z0 Z0 Z0 4E emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result.len()).to_equal(7)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[0]).to_equal(98)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E P0 is 0xF3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm=011(0F3A) = 0xF3
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[1]).to_equal(243)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E P1 is 0x7D

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111 must-1 pp=01(0x66) = 0x7D
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[2]).to_equal(125)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[3]).to_equal(72)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E opcode is 0x23

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[4]).to_equal(35)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E ModRM is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[5]).to_equal(192)
```

</details>

#### VSHUFF32X4 Z0 Z0 Z0 4E imm8 is 0x4E

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vshuff32x4_zmm(48, 48, 48, 0x4E)
expect(result[6]).to_equal(78)
```

</details>

### AVX-512 emit VSHUFF32X4 zmm31 zmm0 zmm0 0x4E — dest=31 boundary

#### VSHUFF32X4 Z31 Z0 Z0 4E P0 is 0x63

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=0(dest[3]=1) ~X=1 ~B=1 ~R'=0(dest[4]=1) mm=011 = 0x63
val result = emit_avx512_vshuff32x4_zmm(79, 48, 48, 0x4E)
expect(result[1]).to_equal(99)
```

</details>

#### VSHUFF32X4 Z31 Z0 Z0 4E ModRM is 0xF8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vshuff32x4_zmm(79, 48, 48, 0x4E)
expect(result[5]).to_equal(248)
```

</details>

### AVX-512 emit VPERMPS zmm0 index=zmm1 src=zmm0 golden

#### VPERMPS Z0 Z1 Z0 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result.len()).to_equal(6)
```

</details>

#### VPERMPS Z0 Z1 Z0 P0 is 0xF2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 mm=010(0F38) = 0xF2
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[1]).to_equal(242)
```

</details>

#### VPERMPS Z0 Z1 Z0 P1 is 0x75

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1110(zmm1 idx=1) must-1 pp=01(0x66) = 0x75
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[2]).to_equal(117)
```

</details>

#### VPERMPS Z0 Z1 Z0 opcode is 0x16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[4]).to_equal(22)
```

</details>

#### VPERMPS Z0 Z1 Z0 ModRM is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpermps_zmm(48, 49, 48)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VPERMPS src2=zmm31 — X-bit ZMM16-31 rm extension

#### VPERMPS Z0 Z0 Z31 P0 is 0x92

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=0(src2=31→X=1) ~B=0(src2[3]=1) ~R'=1 mm=010 = 0x92
val result = emit_avx512_vpermps_zmm(48, 48, 79)
expect(result[1]).to_equal(146)
```

</details>

#### VPERMPS Z0 Z0 Z31 ModRM is 0xC7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=0 rm=7(31%8) = 0xC7
val result = emit_avx512_vpermps_zmm(48, 48, 79)
expect(result[5]).to_equal(199)
```

</details>

### AVX-512 emit VMAXPS zmm0 zmm0 zmm0 canonical golden

#### VMAXPS Z0 Z0 Z0 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result.len()).to_equal(6)
```

</details>

#### VMAXPS Z0 Z0 Z0 P0 is 0xF1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 mm=001(0F) = 0xF1
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[1]).to_equal(241)
```

</details>

#### VMAXPS Z0 Z0 Z0 P1 is 0x7C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111 must-1 pp=00(none) = 0x7C
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[2]).to_equal(124)
```

</details>

#### VMAXPS Z0 Z0 Z0 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[3]).to_equal(72)
```

</details>

#### VMAXPS Z0 Z0 Z0 opcode is 0x5F

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[4]).to_equal(95)
```

</details>

#### VMAXPS Z0 Z0 Z0 ModRM is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vmaxps_zmm(48, 48, 48)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VMAXPS zmm31 dest — Zd=31 boundary

#### VMAXPS Z31 Z0 Z0 P0 is 0x61

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=0(dest[3]=1) ~X=1 ~B=1 ~R'=0(dest[4]=1) mm=001 = 0x61
val result = emit_avx512_vmaxps_zmm(79, 48, 48)
expect(result[1]).to_equal(97)
```

</details>

#### VMAXPS Z31 Z0 Z0 ModRM is 0xF8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vmaxps_zmm(79, 48, 48)
expect(result[5]).to_equal(248)
```

</details>

### AVX-512 emit VMAXPS src2=zmm31 — Zn=31 X-bit boundary

#### VMAXPS Z0 Z0 Z31 P0 is 0x91

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=0(src2=31 X=1) ~B=0(src2[3]=1) ~R'=1 mm=001 = 0x91
val result = emit_avx512_vmaxps_zmm(48, 48, 79)
expect(result[1]).to_equal(145)
```

</details>

#### VMAXPS Z0 Z0 Z31 ModRM is 0xC7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vmaxps_zmm(48, 48, 79)
expect(result[5]).to_equal(199)
```

</details>

### AVX-512 emit VMINPS zmm0 zmm0 zmm0 canonical golden

#### VMINPS Z0 Z0 Z0 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result.len()).to_equal(6)
```

</details>

#### VMINPS Z0 Z0 Z0 P0 is 0xF1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[1]).to_equal(241)
```

</details>

#### VMINPS Z0 Z0 Z0 P1 is 0x7C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[2]).to_equal(124)
```

</details>

#### VMINPS Z0 Z0 Z0 opcode is 0x5D

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[4]).to_equal(93)
```

</details>

#### VMINPS Z0 Z0 Z0 ModRM is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vminps_zmm(48, 48, 48)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 emit VMINPS src1=zmm31 — Zn=31 V-prime boundary

#### VMINPS Z0 Z31 Z0 P1 is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=0000(src1=31→vvvv_lo4=15) must-1 pp=00 = 0x04
val result = emit_avx512_vminps_zmm(48, 79, 48)
expect(result[2]).to_equal(4)
```

</details>

#### VMINPS Z0 Z31 Z0 P2 is 0x40

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=0(V'=1 for src1=31) aaa=000 = 0x40
val result = emit_avx512_vminps_zmm(48, 79, 48)
expect(result[3]).to_equal(64)
```

</details>

### AVX-512 emit VMAXPS src1=zmm16 — V-prime bit boundary

#### VMAXPS Z0 Z16 Z0 P2 is 0x40

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=0(src1=16 V'=1) aaa=000 = 0x40
val result = emit_avx512_vmaxps_zmm(48, 64, 48)
expect(result[3]).to_equal(64)
```

</details>

#### VMAXPS Z0 Z16 Z0 P1 is 0x7C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: ~vvvv=1111(src1=16→vvvv_lo4=0→not_vvvv=15) pp=00 = 0x7C
val result = emit_avx512_vmaxps_zmm(48, 64, 48)
expect(result[2]).to_equal(124)
```

</details>

### AVX-512 emit VMINPS src2=zmm16 — X-bit without B-bit boundary

#### VMINPS Z0 Z0 Z16 P0 is 0xB1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=0(src2[4]=1) ~B=1(src2[3]=0) ~R'=1 mm=001 = 0xB1 = 177
val result = emit_avx512_vminps_zmm(48, 48, 64)
expect(result[1]).to_equal(177)
```

</details>

#### VMINPS Z0 Z0 Z16 opcode is 0x5D

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vminps_zmm(48, 48, 64)
expect(result[4]).to_equal(93)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_reduction_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX-512 emit VBROADCASTSS zmm0 from xmm0 golden
- AVX-512 emit VBROADCASTSS zmm31 from xmm0 — dest=31 boundary
- AVX-512 emit VSHUFF32X4 zmm0 zmm0 zmm0 0x4E golden
- AVX-512 emit VSHUFF32X4 zmm31 zmm0 zmm0 0x4E — dest=31 boundary
- AVX-512 emit VPERMPS zmm0 index=zmm1 src=zmm0 golden
- AVX-512 emit VPERMPS src2=zmm31 — X-bit ZMM16-31 rm extension
- AVX-512 emit VMAXPS zmm0 zmm0 zmm0 canonical golden
- AVX-512 emit VMAXPS zmm31 dest — Zd=31 boundary
- AVX-512 emit VMAXPS src2=zmm31 — Zn=31 X-bit boundary
- AVX-512 emit VMINPS zmm0 zmm0 zmm0 canonical golden
- AVX-512 emit VMINPS src1=zmm31 — Zn=31 V-prime boundary
- AVX-512 emit VMAXPS src1=zmm16 — V-prime bit boundary
- AVX-512 emit VMINPS src2=zmm16 — X-bit without B-bit boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
