# neon_load_store_spec

> Purpose: Prove that NEON emit_neon_ld1q_16b_immoff golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_load_store_spec

Purpose: Prove that NEON emit_neon_ld1q_16b_immoff golden.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_load_store_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that NEON emit_neon_ld1q_16b_immoff golden.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### NEON emit_neon_ld1q_16b_immoff golden

#### LD1 V0.16B [X0] emits 4 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- LD1 V0.16B [X0] emits 4 bytes
- Verify: LD1 V0.16B [X0] emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.16B [X0] emits 4 bytes")
step("Verify: LD1 V0.16B [X0] emits 4 bytes")
# @req: REQ-COMP-NEON-EMIT-NEON-LD1Q-16B-IMMOFF-GOLDEN-001
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LD1 V0.16B [X0] byte0 is 0x00

- LD1 V0.16B [X0] byte0 is 0x00
- Verify: LD1 V0.16B [X0] byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.16B [X0] byte0 is 0x00")
step("Verify: LD1 V0.16B [X0] byte0 is 0x00")
# bits[7:0]: Rt=0, Rn[2:0]=0
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LD1 V0.16B [X0] byte1 is 0x70

- LD1 V0.16B [X0] byte1 is 0x70
- Verify: LD1 V0.16B [X0] byte1 is 0x70
   - Expected: result[1] equals `112`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.16B [X0] byte1 is 0x70")
step("Verify: LD1 V0.16B [X0] byte1 is 0x70")
# bits[15:8]: opcode=0111 upper in bits[15:12], size=00 in bits[11:10] → 0x70
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[1]).to_equal(112)
```

</details>

#### LD1 V0.16B [X0] byte2 is 0x40

- LD1 V0.16B [X0] byte2 is 0x40
- Verify: LD1 V0.16B [X0] byte2 is 0x40
   - Expected: result[2] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.16B [X0] byte2 is 0x40")
step("Verify: LD1 V0.16B [X0] byte2 is 0x40")
# bits[23:16]: bit23=0 (no post), bit22=L=1, bit21=0, bits[20:16]=Rm=00000 → 0x40
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[2]).to_equal(64)
```

</details>

#### LD1 V0.16B [X0] byte3 is 0x4C

- LD1 V0.16B [X0] byte3 is 0x4C
- Verify: LD1 V0.16B [X0] byte3 is 0x4C
   - Expected: result[3] equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.16B [X0] byte3 is 0x4C")
step("Verify: LD1 V0.16B [X0] byte3 is 0x4C")
# bits[31:24]: bit31=0, bit30=Q=1, bits[29:24]=001100 → 0x4C
val result = emit_neon_ld1q_16b_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### LD1 V1.16B [X0] byte0 encodes Rt=1

- LD1 V1.16B [X0] byte0 encodes Rt=1
- Verify: LD1 V1.16B [X0] byte0 encodes Rt=1
   - Expected: result[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V1.16B [X0] byte0 encodes Rt=1")
step("Verify: LD1 V1.16B [X0] byte0 encodes Rt=1")
# Rt=1 in bits[4:0], Rn=0 → byte0 = 1
val result = emit_neon_ld1q_16b_immoff(1, 0)
expect(result[0]).to_equal(1)
```

</details>

#### LD1 V0.16B [X1] byte0 encodes Rn=1

- LD1 V0.16B [X1] byte0 encodes Rn=1
- Verify: LD1 V0.16B [X1] byte0 encodes Rn=1
   - Expected: result[0] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.16B [X1] byte0 encodes Rn=1")
step("Verify: LD1 V0.16B [X1] byte0 encodes Rn=1")
# Rn=1 in bits[9:5] → byte0 = 0 + (1*32)%256 = 0x20
val result = emit_neon_ld1q_16b_immoff(0, 1)
expect(result[0]).to_equal(32)
```

</details>

### NEON emit_neon_st1q_16b_immoff golden

#### ST1 V0.16B [X0] emits 4 bytes

- ST1 V0.16B [X0] emits 4 bytes
- Verify: ST1 V0.16B [X0] emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.16B [X0] emits 4 bytes")
step("Verify: ST1 V0.16B [X0] emits 4 bytes")
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ST1 V0.16B [X0] byte1 is 0x70

- ST1 V0.16B [X0] byte1 is 0x70
- Verify: ST1 V0.16B [X0] byte1 is 0x70
   - Expected: result[1] equals `112`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.16B [X0] byte1 is 0x70")
step("Verify: ST1 V0.16B [X0] byte1 is 0x70")
# opcode/size same as LD1 16B
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result[1]).to_equal(112)
```

</details>

#### ST1 V0.16B [X0] byte2 is 0x00

- ST1 V0.16B [X0] byte2 is 0x00
- Verify: ST1 V0.16B [X0] byte2 is 0x00
   - Expected: result[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.16B [X0] byte2 is 0x00")
step("Verify: ST1 V0.16B [X0] byte2 is 0x00")
# L=0 (store): bits[23:16]=0x00
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result[2]).to_equal(0)
```

</details>

#### ST1 V0.16B [X0] byte3 is 0x4C

- ST1 V0.16B [X0] byte3 is 0x4C
- Verify: ST1 V0.16B [X0] byte3 is 0x4C
   - Expected: result[3] equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.16B [X0] byte3 is 0x4C")
step("Verify: ST1 V0.16B [X0] byte3 is 0x4C")
val result = emit_neon_st1q_16b_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### ST1 V0.16B vs LD1 V0.16B differ only in byte2 L-bit

- ST1 V0.16B vs LD1 V0.16B differ only in byte2 L-bit
- Verify: ST1 V0.16B vs LD1 V0.16B differ only in byte2 L-bit
   - Expected: ld[2] - st[2] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.16B vs LD1 V0.16B differ only in byte2 L-bit")
step("Verify: ST1 V0.16B vs LD1 V0.16B differ only in byte2 L-bit")
# Store clears L bit (byte2 bit6); Load sets it
val ld = emit_neon_ld1q_16b_immoff(0, 0)
val st = emit_neon_st1q_16b_immoff(0, 0)
expect(ld[2] - st[2]).to_equal(64)
```

</details>

### NEON emit_neon_ld1q_4s_immoff golden

#### LD1 V0.4S [X0] emits 4 bytes

- LD1 V0.4S [X0] emits 4 bytes
- Verify: LD1 V0.4S [X0] emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.4S [X0] emits 4 bytes")
step("Verify: LD1 V0.4S [X0] emits 4 bytes")
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LD1 V0.4S [X0] byte0 is 0x00

- LD1 V0.4S [X0] byte0 is 0x00
- Verify: LD1 V0.4S [X0] byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.4S [X0] byte0 is 0x00")
step("Verify: LD1 V0.4S [X0] byte0 is 0x00")
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LD1 V0.4S [X0] byte1 is 0x78

- LD1 V0.4S [X0] byte1 is 0x78
- Verify: LD1 V0.4S [X0] byte1 is 0x78
   - Expected: result[1] equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.4S [X0] byte1 is 0x78")
step("Verify: LD1 V0.4S [X0] byte1 is 0x78")
# bits[15:8]: opcode=0111 in bits[15:12], size=10 in bits[11:10] → 0111_1000 = 0x78
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[1]).to_equal(120)
```

</details>

#### LD1 V0.4S [X0] byte2 is 0x40

- LD1 V0.4S [X0] byte2 is 0x40
- Verify: LD1 V0.4S [X0] byte2 is 0x40
   - Expected: result[2] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.4S [X0] byte2 is 0x40")
step("Verify: LD1 V0.4S [X0] byte2 is 0x40")
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[2]).to_equal(64)
```

</details>

#### LD1 V0.4S [X0] byte3 is 0x4C

- LD1 V0.4S [X0] byte3 is 0x4C
- Verify: LD1 V0.4S [X0] byte3 is 0x4C
   - Expected: result[3] equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.4S [X0] byte3 is 0x4C")
step("Verify: LD1 V0.4S [X0] byte3 is 0x4C")
val result = emit_neon_ld1q_4s_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### LD1 V31.4S [X0] byte0 encodes Rt=31

- LD1 V31.4S [X0] byte0 encodes Rt=31
- Verify: LD1 V31.4S [X0] byte0 encodes Rt=31
   - Expected: result[0] equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V31.4S [X0] byte0 encodes Rt=31")
step("Verify: LD1 V31.4S [X0] byte0 encodes Rt=31")
# Rt=31 in bits[4:0], Rn=0 → byte0 = 31 = 0x1F
val result = emit_neon_ld1q_4s_immoff(31, 0)
expect(result[0]).to_equal(31)
```

</details>

#### LD1 V0.4S [X1] byte0 encodes Rn=1

- LD1 V0.4S [X1] byte0 encodes Rn=1
- Verify: LD1 V0.4S [X1] byte0 encodes Rn=1
   - Expected: result[0] equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.4S [X1] byte0 encodes Rn=1")
step("Verify: LD1 V0.4S [X1] byte0 encodes Rn=1")
# Rn=1 → bits[9:5]=1 → byte0 = 0 + (1*32) = 32 = 0x20
val result = emit_neon_ld1q_4s_immoff(0, 1)
expect(result[0]).to_equal(32)
```

</details>

#### LD1 V0.4S vs LD1 V0.16B differ only in size field byte1

- LD1 V0.4S vs LD1 V0.16B differ only in size field byte1
- Verify: LD1 V0.4S vs LD1 V0.16B differ only in size field byte1
   - Expected: ls[1] - lb[1] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD1 V0.4S vs LD1 V0.16B differ only in size field byte1")
step("Verify: LD1 V0.4S vs LD1 V0.16B differ only in size field byte1")
# .4S has size=10 (bit9=1 → byte1 bit1=1 = +8); .16B has size=00
val ls = emit_neon_ld1q_4s_immoff(0, 0)
val lb = emit_neon_ld1q_16b_immoff(0, 0)
expect(ls[1] - lb[1]).to_equal(8)
```

</details>

### NEON emit_neon_st1q_4s_immoff golden

#### ST1 V0.4S [X0] emits 4 bytes

- ST1 V0.4S [X0] emits 4 bytes
- Verify: ST1 V0.4S [X0] emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.4S [X0] emits 4 bytes")
step("Verify: ST1 V0.4S [X0] emits 4 bytes")
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ST1 V0.4S [X0] byte1 is 0x78

- ST1 V0.4S [X0] byte1 is 0x78
- Verify: ST1 V0.4S [X0] byte1 is 0x78
   - Expected: result[1] equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.4S [X0] byte1 is 0x78")
step("Verify: ST1 V0.4S [X0] byte1 is 0x78")
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result[1]).to_equal(120)
```

</details>

#### ST1 V0.4S [X0] byte2 is 0x00

- ST1 V0.4S [X0] byte2 is 0x00
- Verify: ST1 V0.4S [X0] byte2 is 0x00
   - Expected: result[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.4S [X0] byte2 is 0x00")
step("Verify: ST1 V0.4S [X0] byte2 is 0x00")
# L=0 → byte2 = 0x00
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result[2]).to_equal(0)
```

</details>

#### ST1 V0.4S [X0] byte3 is 0x4C

- ST1 V0.4S [X0] byte3 is 0x4C
- Verify: ST1 V0.4S [X0] byte3 is 0x4C
   - Expected: result[3] equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.4S [X0] byte3 is 0x4C")
step("Verify: ST1 V0.4S [X0] byte3 is 0x4C")
val result = emit_neon_st1q_4s_immoff(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### ST1 V0.4S vs LD1 V0.4S differ only in byte2 L-bit

- ST1 V0.4S vs LD1 V0.4S differ only in byte2 L-bit
- Verify: ST1 V0.4S vs LD1 V0.4S differ only in byte2 L-bit
   - Expected: ld[2] - st[2] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST1 V0.4S vs LD1 V0.4S differ only in byte2 L-bit")
step("Verify: ST1 V0.4S vs LD1 V0.4S differ only in byte2 L-bit")
val ld = emit_neon_ld1q_4s_immoff(0, 0)
val st = emit_neon_st1q_4s_immoff(0, 0)
expect(ld[2] - st[2]).to_equal(64)
```

</details>

### NEON emit_neon_ld2_4s_post golden

#### LD2 {V0.4S V1.4S} [X0] post32 emits 4 bytes

- LD2 {V0.4S V1.4S} [X0] post32 emits 4 bytes
- Verify: LD2 {V0.4S V1.4S} [X0] post32 emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD2 {V0.4S V1.4S} [X0] post32 emits 4 bytes")
step("Verify: LD2 {V0.4S V1.4S} [X0] post32 emits 4 bytes")
val result = emit_neon_ld2_4s_post(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte0 is 0x00

- LD2 {V0.4S V1.4S} [X0] post32 byte0 is 0x00
- Verify: LD2 {V0.4S V1.4S} [X0] post32 byte0 is 0x00
   - Expected: result[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD2 {V0.4S V1.4S} [X0] post32 byte0 is 0x00")
step("Verify: LD2 {V0.4S V1.4S} [X0] post32 byte0 is 0x00")
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88

- LD2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88
- Verify: LD2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88
   - Expected: result[1] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88")
step("Verify: LD2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88")
# bits[15:8]: opcode=1000 in bits[15:12], size=10 in bits[11:10] → 1000_1000 = 0x88
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[1]).to_equal(136)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte2 is 0xDF

- LD2 {V0.4S V1.4S} [X0] post32 byte2 is 0xDF
- Verify: LD2 {V0.4S V1.4S} [X0] post32 byte2 is 0xDF
   - Expected: result[2] equals `223`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD2 {V0.4S V1.4S} [X0] post32 byte2 is 0xDF")
step("Verify: LD2 {V0.4S V1.4S} [X0] post32 byte2 is 0xDF")
# bits[23:16]: bit23=1 (post), bit22=L=1, bit21=0, bits[20:16]=Rm=11111 → 1101_1111=0xDF
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[2]).to_equal(223)
```

</details>

#### LD2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C

- LD2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C
- Verify: LD2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C
   - Expected: result[3] equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C")
step("Verify: LD2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C")
val result = emit_neon_ld2_4s_post(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### LD2 V1.4S [X0] post32 byte0 encodes Rt=1

- LD2 V1.4S [X0] post32 byte0 encodes Rt=1
- Verify: LD2 V1.4S [X0] post32 byte0 encodes Rt=1
   - Expected: result[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("LD2 V1.4S [X0] post32 byte0 encodes Rt=1")
step("Verify: LD2 V1.4S [X0] post32 byte0 encodes Rt=1")
# Rt=1 in bits[4:0] → byte0=1
val result = emit_neon_ld2_4s_post(1, 0)
expect(result[0]).to_equal(1)
```

</details>

### NEON emit_neon_st2_4s_post golden

#### ST2 {V0.4S V1.4S} [X0] post32 emits 4 bytes

- ST2 {V0.4S V1.4S} [X0] post32 emits 4 bytes
- Verify: ST2 {V0.4S V1.4S} [X0] post32 emits 4 bytes
   - Expected: result.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST2 {V0.4S V1.4S} [X0] post32 emits 4 bytes")
step("Verify: ST2 {V0.4S V1.4S} [X0] post32 emits 4 bytes")
val result = emit_neon_st2_4s_post(0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ST2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88

- ST2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88
- Verify: ST2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88
   - Expected: result[1] equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88")
step("Verify: ST2 {V0.4S V1.4S} [X0] post32 byte1 is 0x88")
# Same opcode+size as LD2; differs only in L-bit
val result = emit_neon_st2_4s_post(0, 0)
expect(result[1]).to_equal(136)
```

</details>

#### ST2 {V0.4S V1.4S} [X0] post32 byte2 is 0x9F

- ST2 {V0.4S V1.4S} [X0] post32 byte2 is 0x9F
- Verify: ST2 {V0.4S V1.4S} [X0] post32 byte2 is 0x9F
   - Expected: result[2] equals `159`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST2 {V0.4S V1.4S} [X0] post32 byte2 is 0x9F")
step("Verify: ST2 {V0.4S V1.4S} [X0] post32 byte2 is 0x9F")
# bits[23:16]: 1_0_0_11111 = 0x9F (L=0 for store)
val result = emit_neon_st2_4s_post(0, 0)
expect(result[2]).to_equal(159)
```

</details>

#### ST2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C

- ST2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C
- Verify: ST2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C
   - Expected: result[3] equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C")
step("Verify: ST2 {V0.4S V1.4S} [X0] post32 byte3 is 0x4C")
val result = emit_neon_st2_4s_post(0, 0)
expect(result[3]).to_equal(76)
```

</details>

#### ST2 vs LD2 differ only in byte2 L-bit

- ST2 vs LD2 differ only in byte2 L-bit
- Verify: ST2 vs LD2 differ only in byte2 L-bit
   - Expected: ld[2] - st[2] equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ST2 vs LD2 differ only in byte2 L-bit")
step("Verify: ST2 vs LD2 differ only in byte2 L-bit")
# LD2 byte2=0xDF=223, ST2 byte2=0x9F=159; difference = 64 (bit6 = L)
val ld = emit_neon_ld2_4s_post(0, 0)
val st = emit_neon_st2_4s_post(0, 0)
expect(ld[2] - st[2]).to_equal(64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-NEON-EMIT-NEON-LD1Q-16B-IMMOFF-GOLDEN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2cb43010cfdd210dc38ecde7be8d5b007c76065f37a6bed862a3d6400faa8c12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2cb43010cfdd210dc38ecde7be8d5b007c76065f37a6bed862a3d6400faa8c12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2cb43010cfdd210dc38ecde7be8d5b007c76065f37a6bed862a3d6400faa8c12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_load_store_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_load_store_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_load_store_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_load_store_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_load_store_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 36 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_load_store_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LD1 V0.16B [X0] emits 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_load_store_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LD1 V0.16B [X0] byte0 is 0x00' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_load_store_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LD1 V0.16B [X0] byte1 is 0x70' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
