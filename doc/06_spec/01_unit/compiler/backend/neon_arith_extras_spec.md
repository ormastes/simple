# neon_arith_extras_spec

> Purpose: Prove that NEON emit_neon_vsubq_f32 f32 golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_arith_extras_spec

Purpose: Prove that NEON emit_neon_vsubq_f32 f32 golden.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_arith_extras_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that NEON emit_neon_vsubq_f32 f32 golden.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### NEON emit_neon_vsubq_f32 f32 golden

#### FSUB V0.4S V0.4S V0.4S emits 4 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FSUB V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FSUB V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FSUB V0.4S V0.4S V0.4S emits 4 bytes")
# @req: REQ-COMP-NEON-EMIT-NEON-VSUBQ-F32-F32-GOLDEN-001
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte0 is 0x00

- FSUB V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FSUB V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FSUB V0.4S V0.4S V0.4S byte0 is 0x00")
# Rd=0, Rn=0 → bits[9:0]=0 → byte0=0x00
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte1 is 0xD4

- FSUB V0.4S V0.4S V0.4S byte1 is 0xD4
- Verify: FSUB V0.4S V0.4S V0.4S byte1 is 0xD4
   - Expected: result[1] equals `212`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V0.4S V0.4S V0.4S byte1 is 0xD4")
step("Verify: FSUB V0.4S V0.4S V0.4S byte1 is 0xD4")
# opcode=11010(26) → bits[15:11]; bit10=1 → byte1 = 26*8+4 = 212 = 0xD4
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[1]).to_equal(212)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte2 is 0xA0

- FSUB V0.4S V0.4S V0.4S byte2 is 0xA0
- Verify: FSUB V0.4S V0.4S V0.4S byte2 is 0xA0
   - Expected: result[2] equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V0.4S V0.4S V0.4S byte2 is 0xA0")
step("Verify: FSUB V0.4S V0.4S V0.4S byte2 is 0xA0")
# sz=1 → bit23=1; Rm=0 → bits[20:16]=0 → byte2 = 0xA0
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[2]).to_equal(160)
```

</details>

#### FSUB V0.4S V0.4S V0.4S byte3 is 0x4E

- FSUB V0.4S V0.4S V0.4S byte3 is 0x4E
- Verify: FSUB V0.4S V0.4S V0.4S byte3 is 0x4E
   - Expected: result[3] equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V0.4S V0.4S V0.4S byte3 is 0x4E")
step("Verify: FSUB V0.4S V0.4S V0.4S byte3 is 0x4E")
# Q=1 U=0 → 0x4E (bits[31:24])
val result = emit_neon_vsubq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FSUB V1.4S V2.4S V3.4S byte0 encodes Rd and Rn

- FSUB V1.4S V2.4S V3.4S byte0 encodes Rd and Rn
- Verify: FSUB V1.4S V2.4S V3.4S byte0 encodes Rd and Rn
   - Expected: result[0] equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V1.4S V2.4S V3.4S byte0 encodes Rd and Rn")
step("Verify: FSUB V1.4S V2.4S V3.4S byte0 encodes Rd and Rn")
# inst = 0x4EA0D400 + 1 + 2*32 + 3*65536 = 0x4EA0D400 + 196673 = 0x4ED0D441
# byte0 = 0x41 = 65
val result = emit_neon_vsubq_f32(1, 2, 3)
expect(result[0]).to_equal(65)
```

</details>

#### FSUB V1.4S V2.4S V3.4S byte2 encodes Rm

- FSUB V1.4S V2.4S V3.4S byte2 encodes Rm
- Verify: FSUB V1.4S V2.4S V3.4S byte2 encodes Rm
   - Expected: result[2] equals `163`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V1.4S V2.4S V3.4S byte2 encodes Rm")
step("Verify: FSUB V1.4S V2.4S V3.4S byte2 encodes Rm")
# Rm=3 in bits[20:16]: byte2 = 0xA0 + 3 = 0xA3 = 163
val result = emit_neon_vsubq_f32(1, 2, 3)
expect(result[2]).to_equal(163)
```

</details>

#### FSUB V31.4S V31.4S V31.4S all-ones register boundary

- FSUB V31.4S V31.4S V31.4S all-ones register boundary
- Verify: FSUB V31.4S V31.4S V31.4S all-ones register boundary
   - Expected: result[0] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V31.4S V31.4S V31.4S all-ones register boundary")
step("Verify: FSUB V31.4S V31.4S V31.4S all-ones register boundary")
# inst = 0x4EA0D400 + 31 + 31*32 + 31*65536 = 0x4EBFD7FF
# byte0=0xFF=255, byte1=0xD7=215, byte2=0xBF=191, byte3=0x4E=78
val result = emit_neon_vsubq_f32(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### FSUB V31.4S V31.4S V31.4S byte2 boundary

- FSUB V31.4S V31.4S V31.4S byte2 boundary
- Verify: FSUB V31.4S V31.4S V31.4S byte2 boundary
   - Expected: result[2] equals `191`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FSUB V31.4S V31.4S V31.4S byte2 boundary")
step("Verify: FSUB V31.4S V31.4S V31.4S byte2 boundary")
val result = emit_neon_vsubq_f32(31, 31, 31)
expect(result[2]).to_equal(191)
```

</details>

### NEON emit_neon_vminq_f32 f32 golden

#### FMIN V0.4S V0.4S V0.4S emits 4 bytes

- FMIN V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FMIN V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMIN V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FMIN V0.4S V0.4S V0.4S emits 4 bytes")
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte0 is 0x00

- FMIN V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FMIN V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMIN V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FMIN V0.4S V0.4S V0.4S byte0 is 0x00")
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte1 is 0xF4

- FMIN V0.4S V0.4S V0.4S byte1 is 0xF4
- Verify: FMIN V0.4S V0.4S V0.4S byte1 is 0xF4
   - Expected: result[1] equals `244`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMIN V0.4S V0.4S V0.4S byte1 is 0xF4")
step("Verify: FMIN V0.4S V0.4S V0.4S byte1 is 0xF4")
# opcode=11110(30) → byte1 = 30*8+4 = 244 = 0xF4
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[1]).to_equal(244)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte2 is 0xA0

- FMIN V0.4S V0.4S V0.4S byte2 is 0xA0
- Verify: FMIN V0.4S V0.4S V0.4S byte2 is 0xA0
   - Expected: result[2] equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMIN V0.4S V0.4S V0.4S byte2 is 0xA0")
step("Verify: FMIN V0.4S V0.4S V0.4S byte2 is 0xA0")
# sz=1 → bit23=1; Rm=0 → byte2 = 0xA0 = 160
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[2]).to_equal(160)
```

</details>

#### FMIN V0.4S V0.4S V0.4S byte3 is 0x4E

- FMIN V0.4S V0.4S V0.4S byte3 is 0x4E
- Verify: FMIN V0.4S V0.4S V0.4S byte3 is 0x4E
   - Expected: result[3] equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMIN V0.4S V0.4S V0.4S byte3 is 0x4E")
step("Verify: FMIN V0.4S V0.4S V0.4S byte3 is 0x4E")
val result = emit_neon_vminq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FMIN V0.4S V1.4S V0.4S byte0 encodes Rn

- FMIN V0.4S V1.4S V0.4S byte0 encodes Rn
- Verify: FMIN V0.4S V1.4S V0.4S byte0 encodes Rn
   - Expected: result[0] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMIN V0.4S V1.4S V0.4S byte0 encodes Rn")
step("Verify: FMIN V0.4S V1.4S V0.4S byte0 encodes Rn")
# inst = 0x4EA0F400 + 0 + 1*32 + 0 = 0x4EA0F420
# byte0 = 0x20 = 32
val result = emit_neon_vminq_f32(0, 1, 0)
expect(result[0]).to_equal(32)
```

</details>

### NEON emit_neon_vmaxq_f32 f32 golden

#### FMAX V0.4S V0.4S V0.4S emits 4 bytes

- FMAX V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FMAX V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMAX V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FMAX V0.4S V0.4S V0.4S emits 4 bytes")
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte0 is 0x00

- FMAX V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FMAX V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMAX V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FMAX V0.4S V0.4S V0.4S byte0 is 0x00")
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte1 is 0xF4

- FMAX V0.4S V0.4S V0.4S byte1 is 0xF4
- Verify: FMAX V0.4S V0.4S V0.4S byte1 is 0xF4
   - Expected: result[1] equals `244`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMAX V0.4S V0.4S V0.4S byte1 is 0xF4")
step("Verify: FMAX V0.4S V0.4S V0.4S byte1 is 0xF4")
# opcode=11110(30) → byte1 = 30*8+4 = 244 = 0xF4
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[1]).to_equal(244)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte2 is 0x20

- FMAX V0.4S V0.4S V0.4S byte2 is 0x20
- Verify: FMAX V0.4S V0.4S V0.4S byte2 is 0x20
   - Expected: result[2] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMAX V0.4S V0.4S V0.4S byte2 is 0x20")
step("Verify: FMAX V0.4S V0.4S V0.4S byte2 is 0x20")
# sz=0 → bit23=0; Rm=0 → byte2 = 0x20 = 32
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FMAX V0.4S V0.4S V0.4S byte3 is 0x4E

- FMAX V0.4S V0.4S V0.4S byte3 is 0x4E
- Verify: FMAX V0.4S V0.4S V0.4S byte3 is 0x4E
   - Expected: result[3] equals `78`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMAX V0.4S V0.4S V0.4S byte3 is 0x4E")
step("Verify: FMAX V0.4S V0.4S V0.4S byte3 is 0x4E")
val result = emit_neon_vmaxq_f32(0, 0, 0)
expect(result[3]).to_equal(78)
```

</details>

#### FMAX V0.4S V0.4S V1.4S byte2 encodes Rm

- FMAX V0.4S V0.4S V1.4S byte2 encodes Rm
- Verify: FMAX V0.4S V0.4S V1.4S byte2 encodes Rm
   - Expected: result[2] equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FMAX V0.4S V0.4S V1.4S byte2 encodes Rm")
step("Verify: FMAX V0.4S V0.4S V1.4S byte2 encodes Rm")
# inst = 0x4E20F400 + 0 + 0 + 1*65536 = 0x4E21F400
# byte2 = 0x21 = 33
val result = emit_neon_vmaxq_f32(0, 0, 1)
expect(result[2]).to_equal(33)
```

</details>

### NEON emit_neon_vcgtq_f32 f32 golden

#### FCMGT V0.4S V0.4S V0.4S emits 4 bytes

- FCMGT V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FCMGT V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FCMGT V0.4S V0.4S V0.4S emits 4 bytes")
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte0 is 0x00

- FCMGT V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FCMGT V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FCMGT V0.4S V0.4S V0.4S byte0 is 0x00")
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte1 is 0xE4

- FCMGT V0.4S V0.4S V0.4S byte1 is 0xE4
- Verify: FCMGT V0.4S V0.4S V0.4S byte1 is 0xE4
   - Expected: result[1] equals `228`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S V0.4S V0.4S byte1 is 0xE4")
step("Verify: FCMGT V0.4S V0.4S V0.4S byte1 is 0xE4")
# opcode=11100(28) → byte1 = 28*8+4 = 228 = 0xE4
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[1]).to_equal(228)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte2 is 0xA0

- FCMGT V0.4S V0.4S V0.4S byte2 is 0xA0
- Verify: FCMGT V0.4S V0.4S V0.4S byte2 is 0xA0
   - Expected: result[2] equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S V0.4S V0.4S byte2 is 0xA0")
step("Verify: FCMGT V0.4S V0.4S V0.4S byte2 is 0xA0")
# U=1 sz=1 → bit29=1 bit23=1; Rm=0 → byte2=0xA0=160
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[2]).to_equal(160)
```

</details>

#### FCMGT V0.4S V0.4S V0.4S byte3 is 0x6E

- FCMGT V0.4S V0.4S V0.4S byte3 is 0x6E
- Verify: FCMGT V0.4S V0.4S V0.4S byte3 is 0x6E
   - Expected: result[3] equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S V0.4S V0.4S byte3 is 0x6E")
step("Verify: FCMGT V0.4S V0.4S V0.4S byte3 is 0x6E")
# Q=1 U=1 → 0x6E (bits[31:24])
val result = emit_neon_vcgtq_f32(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### FCMGT V0.4S V1.4S V2.4S byte0 encodes Rn (V-25: Vn>Vm form)

- FCMGT V0.4S V1.4S V2.4S byte0 encodes Rn (V-25: Vn>Vm form)
- Verify: FCMGT V0.4S V1.4S V2.4S byte0 encodes Rn (V-25: Vn>Vm form)
   - Expected: result[0] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S V1.4S V2.4S byte0 encodes Rn (V-25: Vn>Vm form)")
step("Verify: FCMGT V0.4S V1.4S V2.4S byte0 encodes Rn (V-25: Vn>Vm form)")
# inst = 0x6EA0E400 + 0 + 1*32 + 2*65536 = 0x6EC0E420
# byte0 = 0x20 = 32
val result = emit_neon_vcgtq_f32(0, 1, 2)
expect(result[0]).to_equal(32)
```

</details>

#### FCMGT V0.4S V1.4S V2.4S byte2 encodes Rm

- FCMGT V0.4S V1.4S V2.4S byte2 encodes Rm
- Verify: FCMGT V0.4S V1.4S V2.4S byte2 encodes Rm
   - Expected: result[2] equals `162`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S V1.4S V2.4S byte2 encodes Rm")
step("Verify: FCMGT V0.4S V1.4S V2.4S byte2 encodes Rm")
# Rm=2 in bits[20:16]: byte2 = 0xA0 + 2 = 0xA2 = 162; but Rn=1 carries into byte2 bits[25:24]...
# Actually byte2 = bits[23:16]: sz(bit23)=1 → 0x80, size[1]=0, size[0]=0, bit21=1 → 0x20 total base = 0xA0
# + Rm=2 in bits[20:16]: byte2 = 0xA0 + 2 = 0xA2 = 162
# Rn bits are in bits[9:5] which falls in byte0/byte1, not byte2.
val result = emit_neon_vcgtq_f32(0, 1, 2)
expect(result[2]).to_equal(162)
```

</details>

#### FCMGT V31.4S V31.4S V31.4S boundary byte0

- FCMGT V31.4S V31.4S V31.4S boundary byte0
- Verify: FCMGT V31.4S V31.4S V31.4S boundary byte0
   - Expected: result[0] equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V31.4S V31.4S V31.4S boundary byte0")
step("Verify: FCMGT V31.4S V31.4S V31.4S boundary byte0")
# inst = 0x6EA0E400 + 31 + 31*32 + 31*65536 = 0x6EBFE7FF
# byte0=0xFF=255
val result = emit_neon_vcgtq_f32(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### FCMGT V31.4S V31.4S V31.4S boundary byte3 is 0x6E

- FCMGT V31.4S V31.4S V31.4S boundary byte3 is 0x6E
- Verify: FCMGT V31.4S V31.4S V31.4S boundary byte3 is 0x6E
   - Expected: result[3] equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V31.4S V31.4S V31.4S boundary byte3 is 0x6E")
step("Verify: FCMGT V31.4S V31.4S V31.4S boundary byte3 is 0x6E")
val result = emit_neon_vcgtq_f32(31, 31, 31)
expect(result[3]).to_equal(110)
```

</details>

### NEON emit_neon_vcgeq_f32 f32 golden

#### FCMGE V0.4S V0.4S V0.4S emits 4 bytes

- FCMGE V0.4S V0.4S V0.4S emits 4 bytes
- Verify: FCMGE V0.4S V0.4S V0.4S emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S V0.4S V0.4S emits 4 bytes")
step("Verify: FCMGE V0.4S V0.4S V0.4S emits 4 bytes")
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte0 is 0x00

- FCMGE V0.4S V0.4S V0.4S byte0 is 0x00
- Verify: FCMGE V0.4S V0.4S V0.4S byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S V0.4S V0.4S byte0 is 0x00")
step("Verify: FCMGE V0.4S V0.4S V0.4S byte0 is 0x00")
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte1 is 0xE4

- FCMGE V0.4S V0.4S V0.4S byte1 is 0xE4
- Verify: FCMGE V0.4S V0.4S V0.4S byte1 is 0xE4
   - Expected: result[1] equals `228`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S V0.4S V0.4S byte1 is 0xE4")
step("Verify: FCMGE V0.4S V0.4S V0.4S byte1 is 0xE4")
# opcode=11100(28) → byte1 = 28*8+4 = 228 = 0xE4
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[1]).to_equal(228)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte2 is 0x20

- FCMGE V0.4S V0.4S V0.4S byte2 is 0x20
- Verify: FCMGE V0.4S V0.4S V0.4S byte2 is 0x20
   - Expected: result[2] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S V0.4S V0.4S byte2 is 0x20")
step("Verify: FCMGE V0.4S V0.4S V0.4S byte2 is 0x20")
# U=1 sz=0 → bit29=1 bit23=0; Rm=0 → byte2=0x20=32
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### FCMGE V0.4S V0.4S V0.4S byte3 is 0x6E

- FCMGE V0.4S V0.4S V0.4S byte3 is 0x6E
- Verify: FCMGE V0.4S V0.4S V0.4S byte3 is 0x6E
   - Expected: result[3] equals `110`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S V0.4S V0.4S byte3 is 0x6E")
step("Verify: FCMGE V0.4S V0.4S V0.4S byte3 is 0x6E")
val result = emit_neon_vcgeq_f32(0, 0, 0)
expect(result[3]).to_equal(110)
```

</details>

#### FCMGE V31.4S V0.4S V0.4S byte0 encodes Rd boundary

- FCMGE V31.4S V0.4S V0.4S byte0 encodes Rd boundary
- Verify: FCMGE V31.4S V0.4S V0.4S byte0 encodes Rd boundary
   - Expected: result[0] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V31.4S V0.4S V0.4S byte0 encodes Rd boundary")
step("Verify: FCMGE V31.4S V0.4S V0.4S byte0 encodes Rd boundary")
# inst = 0x6E20E400 + 31 = 0x6E20E41F → byte0=0x1F=31
val result = emit_neon_vcgeq_f32(31, 0, 0)
expect(result[0]).to_equal(31)
```

</details>

#### FCMGE V0.4S V2.4S V1.4S byte0 encodes Rn swapped operands

- FCMGE V0.4S V2.4S V1.4S byte0 encodes Rn swapped operands
- Verify: FCMGE V0.4S V2.4S V1.4S byte0 encodes Rn swapped operands
   - Expected: result[0] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S V2.4S V1.4S byte0 encodes Rn swapped operands")
step("Verify: FCMGE V0.4S V2.4S V1.4S byte0 encodes Rn swapped operands")
# V-25 example: cmp_le(V1, V2) → FCMGE(rd, V2, V1)
# inst = 0x6E20E400 + 0 + 2*32 + 1*65536 = 0x6E30E440
# byte0 = 0x40 = 64
val result = emit_neon_vcgeq_f32(0, 2, 1)
expect(result[0]).to_equal(64)
```

</details>

#### FCMGE V0.4S V2.4S V1.4S byte2 encodes Rm

- FCMGE V0.4S V2.4S V1.4S byte2 encodes Rm
- Verify: FCMGE V0.4S V2.4S V1.4S byte2 encodes Rm
   - Expected: result[2] equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S V2.4S V1.4S byte2 encodes Rm")
step("Verify: FCMGE V0.4S V2.4S V1.4S byte2 encodes Rm")
# Rm=1 in bits[20:16]: byte2 = 0x20 + 1 = 0x21 = 33
val result = emit_neon_vcgeq_f32(0, 2, 1)
expect(result[2]).to_equal(33)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-NEON-EMIT-NEON-VSUBQ-F32-F32-GOLDEN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fdc5f0bfda748aeb328cb3a9b6a5d72f5a49807a52ad3284af001f64b01b6ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fdc5f0bfda748aeb328cb3a9b6a5d72f5a49807a52ad3284af001f64b01b6ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fdc5f0bfda748aeb328cb3a9b6a5d72f5a49807a52ad3284af001f64b01b6ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_arith_extras_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_arith_extras_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_arith_extras_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_arith_extras_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_arith_extras_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 38 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_arith_extras_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FSUB V0.4S V0.4S V0.4S emits 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_arith_extras_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FSUB V0.4S V0.4S V0.4S byte0 is 0x00' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_arith_extras_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FSUB V0.4S V0.4S V0.4S byte1 is 0xD4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
