# Neon Load Store Specification

> <details>

<!-- sdn-diagram:id=neon_load_store_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_load_store_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_load_store_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_load_store_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Load Store Specification

## Scenarios

### NEON emit_neon_ld1q_16b_immoff golden

#### LD1 V0.16B [X0] emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LD1 V0.16B [X0] byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[7:0]: Rt=0, Rn[2:0]=0
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LD1 V0.16B [X0] byte1 is 0x70

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode=0111 upper in bits[15:12], size=00 in bits[11:10] → 0x70
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[1]).to_equal(112)
```

</details>

#### LD1 V0.16B [X0] byte2 is 0x40

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]: bit23=0 (no post), bit22=L=1, bit21=0, bits[20:16]=Rm=00000 → 0x40
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[2]).to_equal(64)
```

</details>

#### LD1 V0.16B [X0] byte3 is 0x4C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]: bit31=0, bit30=Q=1, bits[29:24]=001100 → 0x4C
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### LD1 V1.16B [X0] byte0 encodes Rt=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rt=1 in bits[4:0], Rn=0 → byte0 = 1
val result = emit_neon_ld1q_16b_immoff(1, 0)
expect(result[0]).to_equal(1)
```

</details>

#### LD1 V0.16B [X1] byte0 encodes Rn=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rn=1 in bits[9:5] → byte0 = 0 + (1*32)%256 = 0x20
val result = emit_neon_ld1q_16b_immoff(0, 1)
expect(result[0]).to_equal(32)
```

</details>

### NEON emit_neon_st1q_16b_immoff golden

#### ST1 V0.16B [X0] emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ST1 V0.16B [X0] byte1 is 0x70

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# opcode/size same as LD1 16B
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result[1]).to_equal(112)
```

</details>

#### ST1 V0.16B [X0] byte2 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# L=0 (store): bits[23:16]=0x00
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result[2]).to_equal(0)
```

</details>

#### ST1 V0.16B [X0] byte3 is 0x4C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### ST1 V0.16B vs LD1 V0.16B differ only in byte2 L-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Store clears L bit (byte2 bit6); Load sets it
val ld = emit_neon_ld1q_16b_immoff(0, 0)
val st = emit_neon_st1q_16b_immoff(0, 0)
expect(ld[2] - st[2]).to_equal(64)
```

</details>

### NEON emit_neon_ld1q_4s_immoff golden

#### LD1 V0.4S [X0] emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LD1 V0.4S [X0] byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LD1 V0.4S [X0] byte1 is 0x78

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode=0111 in bits[15:12], size=10 in bits[11:10] → 0111_1000 = 0x78
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[1]).to_equal(120)
```

</details>

#### LD1 V0.4S [X0] byte2 is 0x40

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[2]).to_equal(64)
```

</details>

#### LD1 V0.4S [X0] byte3 is 0x4C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### LD1 V31.4S [X0] byte0 encodes Rt=31

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rt=31 in bits[4:0], Rn=0 → byte0 = 31 = 0x1F
val result = emit_neon_ld1q_4s_immoff(31, 0)
expect(result[0]).to_equal(31)
```

</details>

#### LD1 V0.4S [X1] byte0 encodes Rn=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rn=1 → bits[9:5]=1 → byte0 = 0 + (1*32) = 32 = 0x20
val result = emit_neon_ld1q_4s_immoff(0, 1)
expect(result[0]).to_equal(32)
```

</details>

#### LD1 V0.4S vs LD1 V0.16B differ only in size field byte1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# .4S has size=10 (bit9=1 → byte1 bit1=1 = +8); .16B has size=00
val ls = emit_neon_ld1q_4s_immoff(0, 0)
val lb = emit_neon_ld1q_16b_immoff(0, 0)
expect(ls[1] - lb[1]).to_equal(8)
```

</details>

### NEON emit_neon_st1q_4s_immoff golden

#### ST1 V0.4S [X0] emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ST1 V0.4S [X0] byte1 is 0x78

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result[1]).to_equal(120)
```

</details>

#### ST1 V0.4S [X0] byte2 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# L=0 → byte2 = 0x00
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result[2]).to_equal(0)
```

</details>

#### ST1 V0.4S [X0] byte3 is 0x4C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### ST1 V0.4S vs LD1 V0.4S differ only in byte2 L-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ld = emit_neon_ld1q_4s_immoff(0, 0)
val st = emit_neon_st1q_4s_immoff(0, 0)
expect(ld[2] - st[2]).to_equal(64)
```

</details>

### NEON emit_neon_ld2_4s_post golden

#### LD2 {V0.4S V1.4S} [X0] post32 emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld2_4s_post(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode=1000 in bits[15:12], size=10 in bits[11:10] → 1000_1000 = 0x88
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[1]).to_equal(136)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte2 is 0xDF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]: bit23=1 (post), bit22=L=1, bit21=0, bits[20:16]=Rm=11111 → 1101_1111=0xDF
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[2]).to_equal(223)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### LD2 V1.4S [X0] post32 byte0 encodes Rt=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rt=1 in bits[4:0] → byte0=1
val result = emit_neon_ld2_4s_post(1, 0)
expect(result[0]).to_equal(1)
```

</details>

### NEON emit_neon_st2_4s_post golden

#### ST2 {V0.4S V1.4S} [X0] post32 emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_st2_4s_post(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ST2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same opcode+size as LD2; differs only in L-bit
val result = emit_neon_st2_4s_post(0, 0)
expect(result[1]).to_equal(136)
```

</details>

#### ST2 {V0.4S V1.4S} [X0] post32 byte2 is 0x9F

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]: 1_0_0_11111 = 0x9F (L=0 for store)
val result = emit_neon_st2_4s_post(0, 0)
expect(result[2]).to_equal(159)
```

</details>

#### ST2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_st2_4s_post(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### ST2 vs LD2 differ only in byte2 L-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LD2 byte2=0xDF=223, ST2 byte2=0x9F=159; difference = 64 (bit6 = L)
val ld = emit_neon_ld2_4s_post(0, 0)
val st = emit_neon_st2_4s_post(0, 0)
expect(ld[2] - st[2]).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_load_store_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NEON emit_neon_ld1q_16b_immoff golden
- NEON emit_neon_st1q_16b_immoff golden
- NEON emit_neon_ld1q_4s_immoff golden
- NEON emit_neon_st1q_4s_immoff golden
- NEON emit_neon_ld2_4s_post golden
- NEON emit_neon_st2_4s_post golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
