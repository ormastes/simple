# Neon Emit Specification

> <details>

<!-- sdn-diagram:id=neon_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Emit Specification

## Scenarios

### NEON emit_neon_vaddq_f32 f32 golden

#### FADD V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[7:0]: Rd=0, Rn[2:0]=0
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte1 is 0xD4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode=11010 → 0xD4
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[1]).to_equal(212)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]: bit21=1, Rm=0 → 0x20
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte3 is 0x4E

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]: 0=0, Q=1, U=0, 01110 → 0x4E
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FADD V1.4S V2.4S V3.4S byte0 encodes Rd and Rn low

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rd=1 → bits[4:0]=1; Rn=2 → bits[9:5]=2 → byte0 = 1 + (2*32)%256 = 0x41
val result = emit_neon_vaddq_f32(1, 2, 3)
expect(result[0]).to_equal(65)
```

</details>

#### FADD V1.4S V2.4S V3.4S byte2 encodes Rm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rm=3 → bits[20:16]=3 → byte2 = 0x20 + 3 = 0x23
val result = emit_neon_vaddq_f32(1, 2, 3)
expect(result[2]).to_equal(35)
```

</details>

### NEON emit_neon_vmulq_f32 f32 golden

#### FMUL V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte1 is 0xDC

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode=11011 → 0xDC
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[1]).to_equal(220)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte3 is 0x6E

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]: 0=0, Q=1, U=1, 01110 → 0x6E
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### FMUL V2.4S V1.4S V0.4S byte0 encodes Rd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rd=2, Rn=1 → byte0 = 2 + (1*32)%256 = 0x22
val result = emit_neon_vmulq_f32(2, 1, 0)
expect(result[0]).to_equal(34)
```

</details>

#### FMUL V2.4S V1.4S V0.4S byte3 unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vmulq_f32(2, 1, 0)
expect(result[3]).to_equal(110)
```

</details>

### NEON emit_neon_vfmaq_f32 f32 golden

#### FMLA V0.4S V0.4S V0.4S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte1 is 0xCC

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode=11001 → 0xCC
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[1]).to_equal(204)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte3 is 0x4E

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FMLA V3.4S V1.4S V2.4S byte0 encodes Rd and Rn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rd=3, Rn=1 → byte0 = 3 + (1*32)%256 = 0x23
val result = emit_neon_vfmaq_f32(3, 1, 2)
expect(result[0]).to_equal(35)
```

</details>

#### FMLA V3.4S V1.4S V2.4S byte2 encodes Rm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rm=2 → bits[20:16]=2 → byte2 = 0x20 + 2 = 0x22
val result = emit_neon_vfmaq_f32(3, 1, 2)
expect(result[2]).to_equal(34)
```

</details>

### NEON emit_neon_vbslq_u8 16B golden

#### BSL V0.16B V0.16B V0.16B emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte1 is 0x1C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: opcode=000111 lower → 0x1C
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[1]).to_equal(28)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte2 is 0x60

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]: size=11 (bits[22:21]=11), Rm=0 → 0x60
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[2]).to_equal(96)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte3 is 0x6E

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]: 0=0, Q=1, U=1, 01110 → 0x6E
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### BSL V3.16B V1.16B V2.16B byte0 encodes Rd and Rn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rd=3, Rn=1 → byte0 = 3 + (1*32)%256 = 0x23
val result = emit_neon_vbslq_u8(3, 1, 2)
expect(result[0]).to_equal(35)
```

</details>

#### BSL V3.16B V1.16B V2.16B byte2 encodes Rm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rm=2 → bits[20:16]=2, size=11 → byte2 = 0x60 + 2 = 0x62
val result = emit_neon_vbslq_u8(3, 1, 2)
expect(result[2]).to_equal(98)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NEON emit_neon_vaddq_f32 f32 golden
- NEON emit_neon_vmulq_f32 f32 golden
- NEON emit_neon_vfmaq_f32 f32 golden
- NEON emit_neon_vbslq_u8 16B golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
