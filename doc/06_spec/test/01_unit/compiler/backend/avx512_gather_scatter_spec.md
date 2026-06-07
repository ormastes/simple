# Avx512 Gather Scatter Specification

> <details>

<!-- sdn-diagram:id=avx512_gather_scatter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_gather_scatter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_gather_scatter_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_gather_scatter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx512 Gather Scatter Specification

## Scenarios

### AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 no-disp

#### VPGATHERDD Z0 k1 rax Z1*4 emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 escape is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[0]).to_equal(98)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 P0 is 0xF2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 mm=010 (0F38) = 11110010 = 0xF2 = 242
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[1]).to_equal(242)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 P1 is 0x7D

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111 must-1=1 pp=01 = 01111101 = 0x7D = 125
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[2]).to_equal(125)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 P2 is 0x49

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=001 = 01001001 = 0x49 = 73
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[3]).to_equal(73)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 opcode is 0x90

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[4]).to_equal(144)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 ModRM is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=00 reg=000(zmm0) rm=100(SIB) = 00000100 = 0x04 = 4
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[5]).to_equal(4)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4 SIB is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SIB: ss=10(x4) idx=001(zmm1) base=000(rax) = 10001000 = 0x88 = 136
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 disp8

#### VPGATHERDD Z0 k1 rax Z1*4+8 emits 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result.len()).to_equal(8)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4+8 ModRM is 0x44

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mod=01 = disp8 present
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result[5]).to_equal(68)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4+8 SIB is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result[6]).to_equal(136)
```

</details>

#### VPGATHERDD Z0 k1 rax Z1*4+8 disp8 is 0x02

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# disp8 = 8/4 = 2 (EVEX disp8*N compressed, N=4)
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 8)
expect(result[7]).to_equal(2)
```

</details>

### AVX-512 VPGATHERDD zmm0 k7 rax zmm1 scale4

#### VPGATHERDD Z0 k7 rax Z1*4 emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpgatherdd_zmm(48, 87, 49, 0, 4, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VPGATHERDD Z0 k7 rax Z1*4 P2 is 0x4F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=111 = 01001111 = 0x4F = 79
val result = emit_avx512_vpgatherdd_zmm(48, 87, 49, 0, 4, 0)
expect(result[3]).to_equal(79)
```

</details>

### AVX-512 VPSCATTERDD rax zmm1 scale4 k1 zmm0

#### VPSCATTERDD k1 rax Z1*4 Z0 emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result.len()).to_equal(7)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 escape is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[0]).to_equal(98)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 P0 is 0xF2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[1]).to_equal(242)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 opcode is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[4]).to_equal(160)
```

</details>

#### VPSCATTERDD k1 rax Z1*4 Z0 SIB is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpscatterdd_zmm(81, 49, 0, 4, 0, 48)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VGATHERDPS zmm0 k1 rax zmm1 scale4

#### VGATHERDPS Z0 k1 rax Z1*4 emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vgatherdps_zmm(48, 81, 49, 0, 4, 0)
expect(result.len()).to_equal(7)
```

</details>

#### VGATHERDPS Z0 k1 rax Z1*4 opcode is 0x92

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vgatherdps_zmm(48, 81, 49, 0, 4, 0)
expect(result[4]).to_equal(146)
```

</details>

#### VGATHERDPS Z0 k1 rax Z1*4 SIB is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vgatherdps_zmm(48, 81, 49, 0, 4, 0)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VSCATTERDPS rax zmm1 scale4 k1 zmm0

#### VSCATTERDPS k1 rax Z1*4 Z0 emits 7 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vscatterdps_zmm(81, 49, 0, 4, 0, 48)
expect(result.len()).to_equal(7)
```

</details>

#### VSCATTERDPS k1 rax Z1*4 Z0 opcode is 0xA2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vscatterdps_zmm(81, 49, 0, 4, 0, 48)
expect(result[4]).to_equal(162)
```

</details>

#### VSCATTERDPS k1 rax Z1*4 Z0 SIB is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vscatterdps_zmm(81, 49, 0, 4, 0, 48)
expect(result[6]).to_equal(136)
```

</details>

### AVX-512 VPGATHERDD scale boundary SIB tests

#### VPGATHERDD scale=1 SIB is 0x08

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SIB: ss=00(x1) idx=001(zmm1) base=000(rax) = 00001000 = 0x08 = 8
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 1, 0)
expect(result[6]).to_equal(8)
```

</details>

#### VPGATHERDD scale=2 SIB is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SIB: ss=01(x2) idx=001(zmm1) base=000(rax) = 01001000 = 0x48 = 72
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 2, 0)
expect(result[6]).to_equal(72)
```

</details>

#### VPGATHERDD scale=4 SIB is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SIB: ss=10(x4) idx=001(zmm1) base=000(rax) = 10001000 = 0x88 = 136
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 4, 0)
expect(result[6]).to_equal(136)
```

</details>

#### VPGATHERDD scale=8 SIB is 0xC8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SIB: ss=11(x8) idx=001(zmm1) base=000(rax) = 11001000 = 0xC8 = 200
val result = emit_avx512_vpgatherdd_zmm(48, 81, 49, 0, 8, 0)
expect(result[6]).to_equal(200)
```

</details>

### AVX-512 gather k0 rejection guard

#### VPGATHERDD with k0 returns empty (k0 forbidden)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpgatherdd_zmm(48, 80, 49, 0, 4, 0)
expect(result.len()).to_equal(0)
```

</details>

#### VPSCATTERDD with k0 returns empty (k0 forbidden)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpscatterdd_zmm(80, 49, 0, 4, 0, 48)
expect(result.len()).to_equal(0)
```

</details>

### AVX-512 VPGATHERDD zmm1 k1 rax zmm0 scale4 swapped

#### VPGATHERDD Z1 k1 rax Z0*4 ModRM is 0x0C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=00 reg=001(zmm1) rm=100(SIB) = 00001100 = 0x0C = 12
val result = emit_avx512_vpgatherdd_zmm(49, 81, 48, 0, 4, 0)
expect(result[5]).to_equal(12)
```

</details>

#### VPGATHERDD Z1 k1 rax Z0*4 SIB is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SIB: ss=10(x4) idx=000(zmm0) base=000(rax) = 10000000 = 0x80 = 128
val result = emit_avx512_vpgatherdd_zmm(49, 81, 48, 0, 4, 0)
expect(result[6]).to_equal(128)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_gather_scatter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 no-disp
- AVX-512 VPGATHERDD zmm0 k1 rax zmm1 scale4 disp8
- AVX-512 VPGATHERDD zmm0 k7 rax zmm1 scale4
- AVX-512 VPSCATTERDD rax zmm1 scale4 k1 zmm0
- AVX-512 VGATHERDPS zmm0 k1 rax zmm1 scale4
- AVX-512 VSCATTERDPS rax zmm1 scale4 k1 zmm0
- AVX-512 VPGATHERDD scale boundary SIB tests
- AVX-512 gather k0 rejection guard
- AVX-512 VPGATHERDD zmm1 k1 rax zmm0 scale4 swapped

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
