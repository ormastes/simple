# Neon Arith Extras Specification

> <details>

<!-- sdn-diagram:id=neon_arith_extras_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_arith_extras_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_arith_extras_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_arith_extras_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Arith Extras Specification

## Scenarios

### NEON emit_neon_vsubq_f32 f32 golden

#### FSUB V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rd=0, Rn=0 → bits[9:0]=0 → byte0=0x00
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte1 is 0xD4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# opcode=11010(26) → bits[15:11]; bit10=1 → byte1 = 26*8+4 = 212 = 0xD4
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[1]).to_equal(212)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte2 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# sz=1 → bit23=1; Rm=0 → bits[20:16]=0 → byte2 = 0xA0
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[2]).to_equal(160)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte3 is 0x4E

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Q=1 U=0 → 0x4E (bits[31:24])
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FSUB V1.4S V2.4S V3.4S byte0 encodes Rd and Rn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# inst = 0x4EA0D400 + 1 + 2*32 + 3*65536 = 0x4EA0D400 + 196673 = 0x4ED0D441
# byte0 = 0x41 = 65
val result = emit_neon_vsubq_f32(1, 2, 3)
expect(result[0]).to_equal(65)
```

</details>

#### FSUB V1.4S V2.4S V3.4S byte2 encodes Rm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rm=3 in bits[20:16]: byte2 = 0xA0 + 3 = 0xA3 = 163
val result = emit_neon_vsubq_f32(1, 2, 3)
expect(result[2]).to_equal(163)
```

</details>

#### FSUB V31.4S V31.4S V31.4S all-ones register boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# inst = 0x4EA0D400 + 31 + 31*32 + 31*65536 = 0x4EBFD7FF
# byte0=0xFF=255, byte1=0xD7=215, byte2=0xBF=191, byte3=0x4E=78
val result = emit_neon_vsubq_f32(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### FSUB V31.4S V31.4S V31.4S byte2 boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vsubq_f32(31, 31, 31)
expect(result[2]).to_equal(191)
```

</details>

### NEON emit_neon_vminq_f32 f32 golden

#### FMIN V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte1 is 0xF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# opcode=11110(30) → byte1 = 30*8+4 = 244 = 0xF4
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[1]).to_equal(244)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte2 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# sz=1 → bit23=1; Rm=0 → byte2 = 0xA0 = 160
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[2]).to_equal(160)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte3 is 0x4E

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FMIN V0.4S V1.4S V0.4S byte0 encodes Rn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# inst = 0x4EA0F400 + 0 + 1*32 + 0 = 0x4EA0F420
# byte0 = 0x20 = 32
val result = emit_neon_vminq_f32(0, 1, 0)
expect(result[0]).to_equal(32)
```

</details>

### NEON emit_neon_vmaxq_f32 f32 golden

#### FMAX V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte1 is 0xF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# opcode=11110(30) → byte1 = 30*8+4 = 244 = 0xF4
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[1]).to_equal(244)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# sz=0 → bit23=0; Rm=0 → byte2 = 0x20 = 32
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte3 is 0x4E

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FMAX V0.4S V0.4S V1.4S byte2 encodes Rm

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# inst = 0x4E20F400 + 0 + 0 + 1*65536 = 0x4E21F400
# byte2 = 0x21 = 33
val result = emit_neon_vmaxq_f32(0, 0, 1)
expect(result[2]).to_equal(33)
```

</details>

### NEON emit_neon_vcgtq_f32 f32 golden

#### FCMGT V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte1 is 0xE4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# opcode=11100(28) → byte1 = 28*8+4 = 228 = 0xE4
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[1]).to_equal(228)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte2 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U=1 sz=1 → bit29=1 bit23=1; Rm=0 → byte2=0xA0=160
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[2]).to_equal(160)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte3 is 0x6E

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Q=1 U=1 → 0x6E (bits[31:24])
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### FCMGT V0.4S V1.4S V2.4S byte0 encodes Rn (V-25: Vn>Vm form)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# inst = 0x6EA0E400 + 0 + 1*32 + 2*65536 = 0x6EC0E420
# byte0 = 0x20 = 32
val result = emit_neon_vcgtq_f32(0, 1, 2)
expect(result[0]).to_equal(32)
```

</details>

#### FCMGT V0.4S V1.4S V2.4S byte2 encodes Rm

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rm=2 in bits[20:16]: byte2 = 0xA0 + 2 = 0xA2 = 162; but Rn=1 carries into byte2 bits[25:24]...
# Actually byte2 = bits[23:16]: sz(bit23)=1 → 0x80, size[1]=0, size[0]=0, bit21=1 → 0x20 total base = 0xA0
# + Rm=2 in bits[20:16]: byte2 = 0xA0 + 2 = 0xA2 = 162
# Rn bits are in bits[9:5] which falls in byte0/byte1, not byte2.
val result = emit_neon_vcgtq_f32(0, 1, 2)
expect(result[2]).to_equal(162)
```

</details>

#### FCMGT V31.4S V31.4S V31.4S boundary byte0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# inst = 0x6EA0E400 + 31 + 31*32 + 31*65536 = 0x6EBFE7FF
# byte0=0xFF=255
val result = emit_neon_vcgtq_f32(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### FCMGT V31.4S V31.4S V31.4S boundary byte3 is 0x6E

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vcgtq_f32(31, 31, 31)
expect(result[3]).to_equal(110)
```

</details>

### NEON emit_neon_vcgeq_f32 f32 golden

#### FCMGE V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte1 is 0xE4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# opcode=11100(28) → byte1 = 28*8+4 = 228 = 0xE4
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[1]).to_equal(228)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# U=1 sz=0 → bit29=1 bit23=0; Rm=0 → byte2=0x20=32
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte3 is 0x6E

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### FCMGE V31.4S V0.4S V0.4S byte0 encodes Rd boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# inst = 0x6E20E400 + 31 = 0x6E20E41F → byte0=0x1F=31
val result = emit_neon_vcgeq_f32(31, 0, 0)
expect(result[0]).to_equal(31)
```

</details>

#### FCMGE V0.4S V2.4S V1.4S byte0 encodes Rn swapped operands

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# V-25 example: cmp_le(V1, V2) → FCMGE(rd, V2, V1)
# inst = 0x6E20E400 + 0 + 2*32 + 1*65536 = 0x6E30E440
# byte0 = 0x40 = 64
val result = emit_neon_vcgeq_f32(0, 2, 1)
expect(result[0]).to_equal(64)
```

</details>

#### FCMGE V0.4S V2.4S V1.4S byte2 encodes Rm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rm=1 in bits[20:16]: byte2 = 0x20 + 1 = 0x21 = 33
val result = emit_neon_vcgeq_f32(0, 2, 1)
expect(result[2]).to_equal(33)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_arith_extras_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NEON emit_neon_vsubq_f32 f32 golden
- NEON emit_neon_vminq_f32 f32 golden
- NEON emit_neon_vmaxq_f32 f32 golden
- NEON emit_neon_vcgtq_f32 f32 golden
- NEON emit_neon_vcgeq_f32 f32 golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
