# Avx512 Emit Specification

> <details>

<!-- sdn-diagram:id=avx512_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx512 Emit Specification

## Scenarios

### AVX-512 EVEX emit VADDPS f32 golden

#### VADDPS zmm0 zmm0 zmm0 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result.len()).to_equal(6)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[0]).to_equal(98)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 P0 is 0xF1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 m2=0 m1=0 m0=1 = 0xF1 (mm=001=0F map)
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[1]).to_equal(241)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 P1 is 0x7C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111 must-1 pp=00 = 0x7C
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[2]).to_equal(124)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 0x48
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[3]).to_equal(72)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 opcode is 0x58

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[4]).to_equal(88)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 ModRM is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 EVEX emit VMULPS f32 golden

#### VMULPS zmm0 zmm0 zmm0 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result.len()).to_equal(6)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[0]).to_equal(98)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 P0 is 0xF1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[1]).to_equal(241)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 P1 is 0x7C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[2]).to_equal(124)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[3]).to_equal(72)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 opcode is 0x59

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[4]).to_equal(89)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 ModRM is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 EVEX emit VFMADD213PS f32 golden

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ZMM0=48, ZMM1=49, ZMM2=50, K1=81
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result.len()).to_equal(6)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[0]).to_equal(98)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 P0 is 0xF2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 m2=0 m1=1 m0=0 = 0xF2 (MAP2=0F38)
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[1]).to_equal(242)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 P1 is 0x75

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1110(zmm1) must-1 pp=01(0x66) = 0x75
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[2]).to_equal(117)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 P2 is 0xC9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=1 L'=1 L=0 b=0 ~V'=1 aaa=001 = 0xC9
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[3]).to_equal(201)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 opcode is 0xA8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[4]).to_equal(168)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 ModRM is 0xC2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=0(zmm0) rm=2(zmm2) = 0xC2
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[5]).to_equal(194)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX-512 EVEX emit VADDPS f32 golden
- AVX-512 EVEX emit VMULPS f32 golden
- AVX-512 EVEX emit VFMADD213PS f32 golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
