# Avx512 Mask Emit Specification

> <details>

<!-- sdn-diagram:id=avx512_mask_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=avx512_mask_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

avx512_mask_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=avx512_mask_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Avx512 Mask Emit Specification

## Scenarios

### AVX-512 EVEX emit VPCMPEQD zmm-to-k golden

#### VPCMPEQD k1 zmm0 zmm0 emits 6 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result.len()).to_equal(6)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 escape byte is 0x62

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[0]).to_equal(98)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 P0 is 0xF1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 m2=0 m1=0 m0=1 = 0xF1 (mm=001=0F map)
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[1]).to_equal(241)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 P1 is 0x7D

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P1: W=0 ~vvvv=1111(zmm0) must-1 pp=01(0x66) = 0x7D
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[2]).to_equal(125)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 P2 is 0x48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 0x48
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[3]).to_equal(72)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 opcode is 0x76

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[4]).to_equal(118)
```

</details>

#### VPCMPEQD k1 zmm0 zmm0 ModRM is 0xC8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=1(k1) rm=0(zmm0) = 0xC8
val result = emit_avx512_vpcmpeqd_zmm_to_k(81, 48, 48, 80, false)
expect(result[5]).to_equal(200)
```

</details>

### AVX-512 VEX emit KANDB k-reg 3-op golden

#### KANDB k1 k2 k3 emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KANDB k1 k2 k3 VEX escape is 0xC5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[0]).to_equal(197)
```

</details>

#### KANDB k1 k2 k3 byte1 is 0xED

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# byte1: ~R=1 ~vvvv=1101(k2) L=1 pp=01(66) = 0xED
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KANDB k1 k2 k3 opcode is 0x41

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(65)
```

</details>

#### KANDB k1 k2 k3 ModRM is 0xCB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=1(k1) rm=3(k3) = 0xCB
val result = emit_avx512_kandb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KORB k-reg 3-op golden

#### KORB k1 k2 k3 emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KORB k1 k2 k3 byte1 is 0xED

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KORB k1 k2 k3 opcode is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(69)
```

</details>

#### KORB k1 k2 k3 ModRM is 0xCB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_korb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KXORB k-reg 3-op golden

#### KXORB k1 k2 k3 emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KXORB k1 k2 k3 byte1 is 0xED

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KXORB k1 k2 k3 opcode is 0x47

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(71)
```

</details>

#### KXORB k1 k2 k3 ModRM is 0xCB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kxorb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KANDNB k-reg 3-op golden

#### KANDNB k1 k2 k3 emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result.len()).to_equal(4)
```

</details>

#### KANDNB k1 k2 k3 byte1 is 0xED

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result[1]).to_equal(237)
```

</details>

#### KANDNB k1 k2 k3 opcode is 0x42

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result[2]).to_equal(66)
```

</details>

#### KANDNB k1 k2 k3 ModRM is 0xCB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kandnb_kreg_3op(81, 82, 83)
expect(result[3]).to_equal(203)
```

</details>

### AVX-512 VEX emit KMOVW gpr-to-k golden

#### KMOVW k1 eax emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result.len()).to_equal(4)
```

</details>

#### KMOVW k1 eax VEX escape is 0xC5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[0]).to_equal(197)
```

</details>

#### KMOVW k1 eax byte1 is 0xF8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# byte1: ~R=1 ~vvvv=1111(unused) L=0 pp=00 = 0xF8
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[1]).to_equal(248)
```

</details>

#### KMOVW k1 eax opcode is 0x92

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[2]).to_equal(146)
```

</details>

#### KMOVW k1 eax ModRM is 0xC8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ModRM: mod=11 reg=1(k1) rm=0(eax) = 0xC8
val result = emit_avx512_kmovw_gpr_to_k(81, 0)
expect(result[3]).to_equal(200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/avx512_mask_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AVX-512 EVEX emit VPCMPEQD zmm-to-k golden
- AVX-512 VEX emit KANDB k-reg 3-op golden
- AVX-512 VEX emit KORB k-reg 3-op golden
- AVX-512 VEX emit KXORB k-reg 3-op golden
- AVX-512 VEX emit KANDNB k-reg 3-op golden
- AVX-512 VEX emit KMOVW gpr-to-k golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
