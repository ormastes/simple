# neon_emit_spec

> Purpose: Prove that NEON emit_neon_vaddq_f32 f32 golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_emit_spec

Purpose: Prove that NEON emit_neon_vaddq_f32 f32 golden.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that NEON emit_neon_vaddq_f32 f32 golden.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### NEON emit_neon_vaddq_f32 f32 golden

#### FADD V0.4S V0.4S V0.4S emits 4 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FADD V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FADD V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FADD V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FADD V0.4S V0.4S V0.4S emits 4 bytes")
# @req: REQ-COMP-NEON-EMIT-NEON-VADDQ-F32-F32-GOLDEN-001
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte0 is 0x00

- FADD V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FADD V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FADD V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FADD V0.4S V0.4S V0.4S byte0 is 0x00")
# bits[7:0]: Rd=0, Rn[2:0]=0
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte1 is 0xD4

- FADD V0.4S V0.4S V0.4S byte1 is 0xD4
- Verify: FADD V0.4S V0.4S V0.4S byte1 is 0xD4
   - Expected: result[1] equals `212`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FADD V0.4S V0.4S V0.4S byte1 is 0xD4")
step("Verify: FADD V0.4S V0.4S V0.4S byte1 is 0xD4")
# bits[15:8]: opcode=11010 → 0xD4
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[1]).to_equal(212)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte2 is 0x20

- FADD V0.4S V0.4S V0.4S byte2 is 0x20
- Verify: FADD V0.4S V0.4S V0.4S byte2 is 0x20
   - Expected: result[2] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FADD V0.4S V0.4S V0.4S byte2 is 0x20")
step("Verify: FADD V0.4S V0.4S V0.4S byte2 is 0x20")
# bits[23:16]: bit21=1, Rm=0 → 0x20
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FADD V0.4S V0.4S V0.4S byte3 is 0x4E

- FADD V0.4S V0.4S V0.4S byte3 is 0x4E
- Verify: FADD V0.4S V0.4S V0.4S byte3 is 0x4E
   - Expected: result[3] equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FADD V0.4S V0.4S V0.4S byte3 is 0x4E")
step("Verify: FADD V0.4S V0.4S V0.4S byte3 is 0x4E")
# bits[31:24]: 0=0, Q=1, U=0, 01110 → 0x4E
val result = emit_neon_vaddq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FADD V1.4S V2.4S V3.4S byte0 encodes Rd and Rn low

- FADD V1.4S V2.4S V3.4S byte0 encodes Rd and Rn low
- Verify: FADD V1.4S V2.4S V3.4S byte0 encodes Rd and Rn low
   - Expected: result[0] equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FADD V1.4S V2.4S V3.4S byte0 encodes Rd and Rn low")
step("Verify: FADD V1.4S V2.4S V3.4S byte0 encodes Rd and Rn low")
# Rd=1 → bits[4:0]=1; Rn=2 → bits[9:5]=2 → byte0 = 1 + (2*32)%256 = 0x41
val result = emit_neon_vaddq_f32(1, 2, 3)
expect(result[0]).to_equal(65)
```

</details>

#### FADD V1.4S V2.4S V3.4S byte2 encodes Rm

- FADD V1.4S V2.4S V3.4S byte2 encodes Rm
- Verify: FADD V1.4S V2.4S V3.4S byte2 encodes Rm
   - Expected: result[2] equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FADD V1.4S V2.4S V3.4S byte2 encodes Rm")
step("Verify: FADD V1.4S V2.4S V3.4S byte2 encodes Rm")
# Rm=3 → bits[20:16]=3 → byte2 = 0x20 + 3 = 0x23
val result = emit_neon_vaddq_f32(1, 2, 3)
expect(result[2]).to_equal(35)
```

</details>

### NEON emit_neon_vmulq_f32 f32 golden

#### FMUL V0.4S V0.4S V0.4S emits 4 bytes

- FMUL V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FMUL V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMUL V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FMUL V0.4S V0.4S V0.4S emits 4 bytes")
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte0 is 0x00

- FMUL V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FMUL V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMUL V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FMUL V0.4S V0.4S V0.4S byte0 is 0x00")
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte1 is 0xDC

- FMUL V0.4S V0.4S V0.4S byte1 is 0xDC
- Verify: FMUL V0.4S V0.4S V0.4S byte1 is 0xDC
   - Expected: result[1] equals `220`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMUL V0.4S V0.4S V0.4S byte1 is 0xDC")
step("Verify: FMUL V0.4S V0.4S V0.4S byte1 is 0xDC")
# bits[15:8]: opcode=11011 → 0xDC
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[1]).to_equal(220)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte2 is 0x20

- FMUL V0.4S V0.4S V0.4S byte2 is 0x20
- Verify: FMUL V0.4S V0.4S V0.4S byte2 is 0x20
   - Expected: result[2] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMUL V0.4S V0.4S V0.4S byte2 is 0x20")
step("Verify: FMUL V0.4S V0.4S V0.4S byte2 is 0x20")
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FMUL V0.4S V0.4S V0.4S byte3 is 0x6E

- FMUL V0.4S V0.4S V0.4S byte3 is 0x6E
- Verify: FMUL V0.4S V0.4S V0.4S byte3 is 0x6E
   - Expected: result[3] equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMUL V0.4S V0.4S V0.4S byte3 is 0x6E")
step("Verify: FMUL V0.4S V0.4S V0.4S byte3 is 0x6E")
# bits[31:24]: 0=0, Q=1, U=1, 01110 → 0x6E
val result = emit_neon_vmulq_f32(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### FMUL V2.4S V1.4S V0.4S byte0 encodes Rd

- FMUL V2.4S V1.4S V0.4S byte0 encodes Rd
- Verify: FMUL V2.4S V1.4S V0.4S byte0 encodes Rd
   - Expected: result[0] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMUL V2.4S V1.4S V0.4S byte0 encodes Rd")
step("Verify: FMUL V2.4S V1.4S V0.4S byte0 encodes Rd")
# Rd=2, Rn=1 → byte0 = 2 + (1*32)%256 = 0x22
val result = emit_neon_vmulq_f32(2, 1, 0)
expect(result[0]).to_equal(34)
```

</details>

#### FMUL V2.4S V1.4S V0.4S byte3 unchanged

- FMUL V2.4S V1.4S V0.4S byte3 unchanged
- Verify: FMUL V2.4S V1.4S V0.4S byte3 unchanged
   - Expected: result[3] equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMUL V2.4S V1.4S V0.4S byte3 unchanged")
step("Verify: FMUL V2.4S V1.4S V0.4S byte3 unchanged")
val result = emit_neon_vmulq_f32(2, 1, 0)
expect(result[3]).to_equal(110)
```

</details>

### NEON emit_neon_vfmaq_f32 f32 golden

#### FMLA V0.4S V0.4S V0.4S emits 4 bytes

- FMLA V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FMLA V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMLA V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FMLA V0.4S V0.4S V0.4S emits 4 bytes")
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte0 is 0x00

- FMLA V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FMLA V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMLA V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FMLA V0.4S V0.4S V0.4S byte0 is 0x00")
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte1 is 0xCC

- FMLA V0.4S V0.4S V0.4S byte1 is 0xCC
- Verify: FMLA V0.4S V0.4S V0.4S byte1 is 0xCC
   - Expected: result[1] equals `204`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMLA V0.4S V0.4S V0.4S byte1 is 0xCC")
step("Verify: FMLA V0.4S V0.4S V0.4S byte1 is 0xCC")
# bits[15:8]: opcode=11001 → 0xCC
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[1]).to_equal(204)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte2 is 0x20

- FMLA V0.4S V0.4S V0.4S byte2 is 0x20
- Verify: FMLA V0.4S V0.4S V0.4S byte2 is 0x20
   - Expected: result[2] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMLA V0.4S V0.4S V0.4S byte2 is 0x20")
step("Verify: FMLA V0.4S V0.4S V0.4S byte2 is 0x20")
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FMLA V0.4S V0.4S V0.4S byte3 is 0x4E

- FMLA V0.4S V0.4S V0.4S byte3 is 0x4E
- Verify: FMLA V0.4S V0.4S V0.4S byte3 is 0x4E
   - Expected: result[3] equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMLA V0.4S V0.4S V0.4S byte3 is 0x4E")
step("Verify: FMLA V0.4S V0.4S V0.4S byte3 is 0x4E")
val result = emit_neon_vfmaq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FMLA V3.4S V1.4S V2.4S byte0 encodes Rd and Rn

- FMLA V3.4S V1.4S V2.4S byte0 encodes Rd and Rn
- Verify: FMLA V3.4S V1.4S V2.4S byte0 encodes Rd and Rn
   - Expected: result[0] equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMLA V3.4S V1.4S V2.4S byte0 encodes Rd and Rn")
step("Verify: FMLA V3.4S V1.4S V2.4S byte0 encodes Rd and Rn")
# Rd=3, Rn=1 → byte0 = 3 + (1*32)%256 = 0x23
val result = emit_neon_vfmaq_f32(3, 1, 2)
expect(result[0]).to_equal(35)
```

</details>

#### FMLA V3.4S V1.4S V2.4S byte2 encodes Rm

- FMLA V3.4S V1.4S V2.4S byte2 encodes Rm
- Verify: FMLA V3.4S V1.4S V2.4S byte2 encodes Rm
   - Expected: result[2] equals `34`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMLA V3.4S V1.4S V2.4S byte2 encodes Rm")
step("Verify: FMLA V3.4S V1.4S V2.4S byte2 encodes Rm")
# Rm=2 → bits[20:16]=2 → byte2 = 0x20 + 2 = 0x22
val result = emit_neon_vfmaq_f32(3, 1, 2)
expect(result[2]).to_equal(34)
```

</details>

### NEON emit_neon_vbslq_u8 16B golden

#### BSL V0.16B V0.16B V0.16B emits 4 bytes

- BSL V0.16B V0.16B V0.16B emits 4 bytes
- Verify: BSL V0.16B V0.16B V0.16B emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V0.16B V0.16B V0.16B emits 4 bytes")
step("Verify: BSL V0.16B V0.16B V0.16B emits 4 bytes")
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte0 is 0x00

- BSL V0.16B V0.16B V0.16B byte0 is 0x00
- Verify: BSL V0.16B V0.16B V0.16B byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V0.16B V0.16B V0.16B byte0 is 0x00")
step("Verify: BSL V0.16B V0.16B V0.16B byte0 is 0x00")
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte1 is 0x1C

- BSL V0.16B V0.16B V0.16B byte1 is 0x1C
- Verify: BSL V0.16B V0.16B V0.16B byte1 is 0x1C
   - Expected: result[1] equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V0.16B V0.16B V0.16B byte1 is 0x1C")
step("Verify: BSL V0.16B V0.16B V0.16B byte1 is 0x1C")
# bits[15:8]: opcode=000111 lower → 0x1C
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[1]).to_equal(28)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte2 is 0x60

- BSL V0.16B V0.16B V0.16B byte2 is 0x60
- Verify: BSL V0.16B V0.16B V0.16B byte2 is 0x60
   - Expected: result[2] equals `96`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V0.16B V0.16B V0.16B byte2 is 0x60")
step("Verify: BSL V0.16B V0.16B V0.16B byte2 is 0x60")
# bits[23:16]: size=11 (bits[22:21]=11), Rm=0 → 0x60
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[2]).to_equal(96)
```

</details>

#### BSL V0.16B V0.16B V0.16B byte3 is 0x6E

- BSL V0.16B V0.16B V0.16B byte3 is 0x6E
- Verify: BSL V0.16B V0.16B V0.16B byte3 is 0x6E
   - Expected: result[3] equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V0.16B V0.16B V0.16B byte3 is 0x6E")
step("Verify: BSL V0.16B V0.16B V0.16B byte3 is 0x6E")
# bits[31:24]: 0=0, Q=1, U=1, 01110 → 0x6E
val result = emit_neon_vbslq_u8(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### BSL V3.16B V1.16B V2.16B byte0 encodes Rd and Rn

- BSL V3.16B V1.16B V2.16B byte0 encodes Rd and Rn
- Verify: BSL V3.16B V1.16B V2.16B byte0 encodes Rd and Rn
   - Expected: result[0] equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V3.16B V1.16B V2.16B byte0 encodes Rd and Rn")
step("Verify: BSL V3.16B V1.16B V2.16B byte0 encodes Rd and Rn")
# Rd=3, Rn=1 → byte0 = 3 + (1*32)%256 = 0x23
val result = emit_neon_vbslq_u8(3, 1, 2)
expect(result[0]).to_equal(35)
```

</details>

#### BSL V3.16B V1.16B V2.16B byte2 encodes Rm

- BSL V3.16B V1.16B V2.16B byte2 encodes Rm
- Verify: BSL V3.16B V1.16B V2.16B byte2 encodes Rm
   - Expected: result[2] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V3.16B V1.16B V2.16B byte2 encodes Rm")
step("Verify: BSL V3.16B V1.16B V2.16B byte2 encodes Rm")
# Rm=2 → bits[20:16]=2, size=11 → byte2 = 0x60 + 2 = 0x62
val result = emit_neon_vbslq_u8(3, 1, 2)
expect(result[2]).to_equal(98)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-NEON-EMIT-NEON-VADDQ-F32-F32-GOLDEN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eaa0e7aec25fafd455e94d9d42213f2b866c4fe3dcd410b9e807d92dacd2ffbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eaa0e7aec25fafd455e94d9d42213f2b866c4fe3dcd410b9e807d92dacd2ffbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eaa0e7aec25fafd455e94d9d42213f2b866c4fe3dcd410b9e807d92dacd2ffbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_emit_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_emit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_emit_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FADD V0.4S V0.4S V0.4S emits 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_emit_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FADD V0.4S V0.4S V0.4S byte0 is 0x00' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_emit_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FADD V0.4S V0.4S V0.4S byte1 is 0xD4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
