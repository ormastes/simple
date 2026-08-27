# neon_fp16_spec

> Purpose: Prove that emit_fcvtn_4h — narrow fp32 to fp16 into lower half.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_fp16_spec

Purpose: Prove that emit_fcvtn_4h — narrow fp32 to fp16 into lower half.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_fp16_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_fcvtn_4h — narrow fp32 to fp16 into lower half.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_fcvtn_4h — narrow fp32 to fp16 into lower half

#### FCVTN V0.4H, V0.4S encodes to base opcode bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FCVTN V0.4H, V0.4S encodes to base opcode bytes
- Verify: FCVTN V0.4H, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTN V0.4H, V0.4S encodes to base opcode bytes")
step("Verify: FCVTN V0.4H, V0.4S encodes to base opcode bytes")
# @req: REQ-COMP-EMIT-FCVTN-4H-NARROW-FP32-TO-FP16-INTO-L-001
# word = 0x0E216800 + 0*32 + 0 = 0x0E216800
# LE: [0x00, 0x68, 0x21, 0x0E]
var b = emit_fcvtn_4h(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x0E)
```

</details>

#### FCVTN V0.4H, V1.4S encodes rn=1 into bits[9:5]

- FCVTN V0.4H, V1.4S encodes rn=1 into bits[9:5]
- Verify: FCVTN V0.4H, V1.4S encodes rn=1 into bits[9:5]
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTN V0.4H, V1.4S encodes rn=1 into bits[9:5]")
step("Verify: FCVTN V0.4H, V1.4S encodes rn=1 into bits[9:5]")
# word = 0x0E216800 + 1*32 + 0 = 0x0E216820
# LE: [0x20, 0x68, 0x21, 0x0E]
var b = emit_fcvtn_4h(0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x0E)
```

</details>

#### FCVTN V1.4H, V2.4S encodes rd=1 rn=2 correctly

- FCVTN V1.4H, V2.4S encodes rd=1 rn=2 correctly
- Verify: FCVTN V1.4H, V2.4S encodes rd=1 rn=2 correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTN V1.4H, V2.4S encodes rd=1 rn=2 correctly")
step("Verify: FCVTN V1.4H, V2.4S encodes rd=1 rn=2 correctly")
# word = 0x0E216800 + 2*32 + 1 = 0x0E216841
# LE: [0x41, 0x68, 0x21, 0x0E]
var b = emit_fcvtn_4h(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x0E)
```

</details>

### emit_fcvtn2_8h — narrow fp32 to fp16 into upper half

#### FCVTN2 V0.8H, V0.4S encodes to base opcode bytes

- FCVTN2 V0.8H, V0.4S encodes to base opcode bytes
- Verify: FCVTN2 V0.8H, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTN2 V0.8H, V0.4S encodes to base opcode bytes")
step("Verify: FCVTN2 V0.8H, V0.4S encodes to base opcode bytes")
# word = 0x4E216800 + 0*32 + 0 = 0x4E216800
# LE: [0x00, 0x68, 0x21, 0x4E]
var b = emit_fcvtn2_8h(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCVTN2 V0.8H, V1.4S encodes rn=1

- FCVTN2 V0.8H, V1.4S encodes rn=1
- Verify: FCVTN2 V0.8H, V1.4S encodes rn=1
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTN2 V0.8H, V1.4S encodes rn=1")
step("Verify: FCVTN2 V0.8H, V1.4S encodes rn=1")
# word = 0x4E216800 + 1*32 + 0 = 0x4E216820
# LE: [0x20, 0x68, 0x21, 0x4E]
var b = emit_fcvtn2_8h(0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCVTN2 V3.8H, V4.4S encodes rd=3 rn=4 correctly

- FCVTN2 V3.8H, V4.4S encodes rd=3 rn=4 correctly
- Verify: FCVTN2 V3.8H, V4.4S encodes rd=3 rn=4 correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x83`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTN2 V3.8H, V4.4S encodes rd=3 rn=4 correctly")
step("Verify: FCVTN2 V3.8H, V4.4S encodes rd=3 rn=4 correctly")
# word = 0x4E216800 + 4*32 + 3 = 0x4E216883
# LE: [0x83, 0x68, 0x21, 0x4E]
var b = emit_fcvtn2_8h(3, 4)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x83)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_fcvtl_4s — widen fp16 to fp32 from lower half

#### FCVTL V0.4S, V0.4H encodes to base opcode bytes

- FCVTL V0.4S, V0.4H encodes to base opcode bytes
- Verify: FCVTL V0.4S, V0.4H encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTL V0.4S, V0.4H encodes to base opcode bytes")
step("Verify: FCVTL V0.4S, V0.4H encodes to base opcode bytes")
# word = 0x0E217800 + 0*32 + 0 = 0x0E217800
# LE: [0x00, 0x78, 0x21, 0x0E]
var b = emit_fcvtl_4s(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x0E)
```

</details>

#### FCVTL V0.4S, V1.4H encodes rn=1

- FCVTL V0.4S, V1.4H encodes rn=1
- Verify: FCVTL V0.4S, V1.4H encodes rn=1
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTL V0.4S, V1.4H encodes rn=1")
step("Verify: FCVTL V0.4S, V1.4H encodes rn=1")
# word = 0x0E217800 + 1*32 + 0 = 0x0E217820
# LE: [0x20, 0x78, 0x21, 0x0E]
var b = emit_fcvtl_4s(0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x0E)
```

</details>

#### FCVTL V2.4S, V3.4H encodes rd=2 rn=3 correctly

- FCVTL V2.4S, V3.4H encodes rd=2 rn=3 correctly
- Verify: FCVTL V2.4S, V3.4H encodes rd=2 rn=3 correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x62`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTL V2.4S, V3.4H encodes rd=2 rn=3 correctly")
step("Verify: FCVTL V2.4S, V3.4H encodes rd=2 rn=3 correctly")
# word = 0x0E217800 + 3*32 + 2 = 0x0E217862
# LE: [0x62, 0x78, 0x21, 0x0E]
var b = emit_fcvtl_4s(2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x62)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x0E)
```

</details>

### emit_fcvtl2_4s — widen fp16 to fp32 from upper half

#### FCVTL2 V0.4S, V0.8H encodes to base opcode bytes

- FCVTL2 V0.4S, V0.8H encodes to base opcode bytes
- Verify: FCVTL2 V0.4S, V0.8H encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTL2 V0.4S, V0.8H encodes to base opcode bytes")
step("Verify: FCVTL2 V0.4S, V0.8H encodes to base opcode bytes")
# word = 0x4E217800 + 0*32 + 0 = 0x4E217800
# LE: [0x00, 0x78, 0x21, 0x4E]
var b = emit_fcvtl2_4s(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCVTL2 V0.4S, V1.8H encodes rn=1

- FCVTL2 V0.4S, V1.8H encodes rn=1
- Verify: FCVTL2 V0.4S, V1.8H encodes rn=1
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTL2 V0.4S, V1.8H encodes rn=1")
step("Verify: FCVTL2 V0.4S, V1.8H encodes rn=1")
# word = 0x4E217800 + 1*32 + 0 = 0x4E217820
# LE: [0x20, 0x78, 0x21, 0x4E]
var b = emit_fcvtl2_4s(0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCVTL2 V2.4S, V3.8H encodes rd=2 rn=3 correctly

- FCVTL2 V2.4S, V3.8H encodes rd=2 rn=3 correctly
- Verify: FCVTL2 V2.4S, V3.8H encodes rd=2 rn=3 correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x62`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTL2 V2.4S, V3.8H encodes rd=2 rn=3 correctly")
step("Verify: FCVTL2 V2.4S, V3.8H encodes rd=2 rn=3 correctly")
# word = 0x4E217800 + 3*32 + 2 = 0x4E217862
# LE: [0x62, 0x78, 0x21, 0x4E]
var b = emit_fcvtl2_4s(2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x62)
expect(b[1]).to_equal(0x78)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_fcvtzs_4s — fp32 to signed int32 truncate 4 lanes

#### FCVTZS V0.4S, V0.4S encodes to base opcode bytes

- FCVTZS V0.4S, V0.4S encodes to base opcode bytes
- Verify: FCVTZS V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTZS V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: FCVTZS V0.4S, V0.4S encodes to base opcode bytes")
# word = 0x4EA1B800 + 0*32 + 0 = 0x4EA1B800
# LE: [0x00, 0xB8, 0xA1, 0x4E]
var b = emit_fcvtzs_4s(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xB8)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCVTZS V0.4S, V1.4S encodes rn=1

- FCVTZS V0.4S, V1.4S encodes rn=1
- Verify: FCVTZS V0.4S, V1.4S encodes rn=1
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTZS V0.4S, V1.4S encodes rn=1")
step("Verify: FCVTZS V0.4S, V1.4S encodes rn=1")
# word = 0x4EA1B800 + 1*32 + 0 = 0x4EA1B820
# LE: [0x20, 0xB8, 0xA1, 0x4E]
var b = emit_fcvtzs_4s(0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xB8)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCVTZS V3.4S, V4.4S encodes rd=3 rn=4 correctly

- FCVTZS V3.4S, V4.4S encodes rd=3 rn=4 correctly
- Verify: FCVTZS V3.4S, V4.4S encodes rd=3 rn=4 correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x83`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTZS V3.4S, V4.4S encodes rd=3 rn=4 correctly")
step("Verify: FCVTZS V3.4S, V4.4S encodes rd=3 rn=4 correctly")
# word = 0x4EA1B800 + 4*32 + 3 = 0x4EA1B883
# LE: [0x83, 0xB8, 0xA1, 0x4E]
var b = emit_fcvtzs_4s(3, 4)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x83)
expect(b[1]).to_equal(0xB8)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_fcvtzu_4s — fp32 to unsigned int32 truncate 4 lanes

#### FCVTZU V0.4S, V0.4S encodes to base opcode bytes

- FCVTZU V0.4S, V0.4S encodes to base opcode bytes
- Verify: FCVTZU V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTZU V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: FCVTZU V0.4S, V0.4S encodes to base opcode bytes")
# word = 0x6EA1B800 + 0*32 + 0 = 0x6EA1B800
# LE: [0x00, 0xB8, 0xA1, 0x6E]
var b = emit_fcvtzu_4s(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xB8)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x6E)
```

</details>

#### FCVTZU V0.4S, V1.4S encodes rn=1

- FCVTZU V0.4S, V1.4S encodes rn=1
- Verify: FCVTZU V0.4S, V1.4S encodes rn=1
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTZU V0.4S, V1.4S encodes rn=1")
step("Verify: FCVTZU V0.4S, V1.4S encodes rn=1")
# word = 0x6EA1B800 + 1*32 + 0 = 0x6EA1B820
# LE: [0x20, 0xB8, 0xA1, 0x6E]
var b = emit_fcvtzu_4s(0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xB8)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x6E)
```

</details>

#### FCVTZU V3.4S, V4.4S encodes rd=3 rn=4 correctly

- FCVTZU V3.4S, V4.4S encodes rd=3 rn=4 correctly
- Verify: FCVTZU V3.4S, V4.4S encodes rd=3 rn=4 correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x83`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTZU V3.4S, V4.4S encodes rd=3 rn=4 correctly")
step("Verify: FCVTZU V3.4S, V4.4S encodes rd=3 rn=4 correctly")
# word = 0x6EA1B800 + 4*32 + 3 = 0x6EA1B883
# LE: [0x83, 0xB8, 0xA1, 0x6E]
var b = emit_fcvtzu_4s(3, 4)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x83)
expect(b[1]).to_equal(0xB8)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x6E)
```

</details>

### FP16 conversion emit output length

#### emit_fcvtn_4h always returns 4 bytes

- emit_fcvtn_4h always returns 4 bytes
- Verify: emit_fcvtn_4h always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcvtn_4h always returns 4 bytes")
step("Verify: emit_fcvtn_4h always returns 4 bytes")
var b = emit_fcvtn_4h(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtn2_8h always returns 4 bytes

- emit_fcvtn2_8h always returns 4 bytes
- Verify: emit_fcvtn2_8h always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcvtn2_8h always returns 4 bytes")
step("Verify: emit_fcvtn2_8h always returns 4 bytes")
var b = emit_fcvtn2_8h(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtl_4s always returns 4 bytes

- emit_fcvtl_4s always returns 4 bytes
- Verify: emit_fcvtl_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcvtl_4s always returns 4 bytes")
step("Verify: emit_fcvtl_4s always returns 4 bytes")
var b = emit_fcvtl_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtl2_4s always returns 4 bytes

- emit_fcvtl2_4s always returns 4 bytes
- Verify: emit_fcvtl2_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcvtl2_4s always returns 4 bytes")
step("Verify: emit_fcvtl2_4s always returns 4 bytes")
var b = emit_fcvtl2_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtzs_4s always returns 4 bytes

- emit_fcvtzs_4s always returns 4 bytes
- Verify: emit_fcvtzs_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcvtzs_4s always returns 4 bytes")
step("Verify: emit_fcvtzs_4s always returns 4 bytes")
var b = emit_fcvtzs_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtzu_4s always returns 4 bytes

- emit_fcvtzu_4s always returns 4 bytes
- Verify: emit_fcvtzu_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcvtzu_4s always returns 4 bytes")
step("Verify: emit_fcvtzu_4s always returns 4 bytes")
var b = emit_fcvtzu_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

### FCVTN vs FCVTN2 Q-bit distinction

#### FCVTN and FCVTN2 with same registers match bytes 0-2 and differ at byte[3]

- FCVTN and FCVTN2 with same registers match bytes 0-2 and differ at byte[3]
- Verify: FCVTN and FCVTN2 with same registers match bytes 0-2 and differ at byte[3]
   - Expected: n[0] equals `n2[0]`
   - Expected: n[1] equals `n2[1]`
   - Expected: n[2] equals `n2[2]`
   - Expected: n2[3] - n[3] equals `0x40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTN and FCVTN2 with same registers match bytes 0-2 and differ at byte[3]")
step("Verify: FCVTN and FCVTN2 with same registers match bytes 0-2 and differ at byte[3]")
var n  = emit_fcvtn_4h(0, 1)
var n2 = emit_fcvtn2_8h(0, 1)
expect(n[0]).to_equal(n2[0])
expect(n[1]).to_equal(n2[1])
expect(n[2]).to_equal(n2[2])
# FCVTN2 has Q=1 (bit 30), raising byte[3] by 0x40
expect(n2[3] - n[3]).to_equal(0x40)
```

</details>

### FCVTZS vs FCVTZU U-bit distinction

#### FCVTZS and FCVTZU with same registers match bytes 0-2 and differ at byte[3]

- FCVTZS and FCVTZU with same registers match bytes 0-2 and differ at byte[3]
- Verify: FCVTZS and FCVTZU with same registers match bytes 0-2 and differ at byte[3]
   - Expected: s[0] equals `u[0]`
   - Expected: s[1] equals `u[1]`
   - Expected: s[2] equals `u[2]`
   - Expected: u[3] - s[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCVTZS and FCVTZU with same registers match bytes 0-2 and differ at byte[3]")
step("Verify: FCVTZS and FCVTZU with same registers match bytes 0-2 and differ at byte[3]")
var s = emit_fcvtzs_4s(0, 1)
var u = emit_fcvtzu_4s(0, 1)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# FCVTZU has U=1 (bit 29), raising byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-EMIT-FCVTN-4H-NARROW-FP32-TO-FP16-INTO-L-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a079759b66bc074283fe45514762a7d7cbc91807099279cc2787ee50f782c5a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a079759b66bc074283fe45514762a7d7cbc91807099279cc2787ee50f782c5a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a079759b66bc074283fe45514762a7d7cbc91807099279cc2787ee50f782c5a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_fp16_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_fp16_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_fp16_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_fp16_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_fp16_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_fp16_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FCVTN V0.4H, V0.4S encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_fp16_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FCVTN V0.4H, V1.4S encodes rn=1 into bits[9:5]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_fp16_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FCVTN V1.4H, V2.4S encodes rd=1 rn=2 correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
