# neon_cmp_emit_spec

> Purpose: Prove that emit_cmeq_4s — compare equal 4x32-bit lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_cmp_emit_spec

Purpose: Prove that emit_cmeq_4s — compare equal 4x32-bit lanes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_cmp_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_cmeq_4s — compare equal 4x32-bit lanes.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_cmeq_4s — compare equal 4x32-bit lanes

#### CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x8C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
# @req: REQ-COMP-EMIT-CMEQ-4S-COMPARE-EQUAL-4X32-BIT-LANE-001
var b = emit_cmeq_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x8C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly

- CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x8C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x6EA08C00 | (3 << 16) | (2 << 5) | 1
#      = 0x6EA08C00 | 0x30000 | 0x40 | 1
#      = 0x6EA38C41
# LE: 0x41, 0x8C, 0xA3, 0x6E
var b = emit_cmeq_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x8C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_cmeq_4s always returns 4 bytes

- emit_cmeq_4s always returns 4 bytes
- Verify: emit_cmeq_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_cmeq_4s always returns 4 bytes")
step("Verify: emit_cmeq_4s always returns 4 bytes")
var b = emit_cmeq_4s(4, 5, 6)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmgt_4s — compare signed greater-than 4x32-bit lanes

#### CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_cmgt_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly

- CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x4EA03400 | (3 << 16) | (2 << 5) | 1
#      = 0x4EA03400 | 0x30000 | 0x40 | 1
#      = 0x4EA33441
# LE: 0x41, 0x34, 0xA3, 0x4E
var b = emit_cmgt_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_cmgt_4s always returns 4 bytes

- emit_cmgt_4s always returns 4 bytes
- Verify: emit_cmgt_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_cmgt_4s always returns 4 bytes")
step("Verify: emit_cmgt_4s always returns 4 bytes")
var b = emit_cmgt_4s(7, 8, 9)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmge_4s — compare signed greater-than-or-equal 4x32-bit lanes

#### CMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- CMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: CMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x3C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: CMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_cmge_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x3C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### CMGE V1.4S, V2.4S, V3.4S encodes register fields correctly

- CMGE V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: CMGE V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x3C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMGE V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: CMGE V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x4EA03C00 | (3 << 16) | (2 << 5) | 1
#      = 0x4EA03C00 | 0x30000 | 0x40 | 1
#      = 0x4EA33C41
# LE: 0x41, 0x3C, 0xA3, 0x4E
var b = emit_cmge_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x3C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_cmge_4s always returns 4 bytes

- emit_cmge_4s always returns 4 bytes
- Verify: emit_cmge_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_cmge_4s always returns 4 bytes")
step("Verify: emit_cmge_4s always returns 4 bytes")
var b = emit_cmge_4s(10, 11, 12)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmhi_4s — compare unsigned higher 4x32-bit lanes

#### CMHI V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- CMHI V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: CMHI V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMHI V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: CMHI V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_cmhi_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### CMHI V1.4S, V2.4S, V3.4S encodes register fields correctly

- CMHI V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: CMHI V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CMHI V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: CMHI V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x6EA03400 | (3 << 16) | (2 << 5) | 1
#      = 0x6EA03400 | 0x30000 | 0x40 | 1
#      = 0x6EA33441
# LE: 0x41, 0x34, 0xA3, 0x6E
var b = emit_cmhi_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_cmhi_4s always returns 4 bytes

- emit_cmhi_4s always returns 4 bytes
- Verify: emit_cmhi_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_cmhi_4s always returns 4 bytes")
step("Verify: emit_cmhi_4s always returns 4 bytes")
var b = emit_cmhi_4s(13, 14, 15)
expect(b.len()).to_equal(4)
```

</details>

### emit_fcmeq_4s — fp compare equal 4x32-bit lanes

#### FCMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- FCMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: FCMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: FCMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_fcmeq_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly

- FCMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: FCMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: FCMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x4E20E400 | (3 << 16) | (2 << 5) | 1
#      = 0x4E20E400 | 0x30000 | 0x40 | 1
#      = 0x4E23E441
# LE: 0x41, 0xE4, 0x23, 0x4E
var b = emit_fcmeq_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x23)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_fcmeq_4s always returns 4 bytes

- emit_fcmeq_4s always returns 4 bytes
- Verify: emit_fcmeq_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcmeq_4s always returns 4 bytes")
step("Verify: emit_fcmeq_4s always returns 4 bytes")
var b = emit_fcmeq_4s(16, 17, 18)
expect(b.len()).to_equal(4)
```

</details>

### emit_fcmgt_4s — fp compare greater-than 4x32-bit lanes

#### FCMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- FCMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: FCMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: FCMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_fcmgt_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### FCMGT V1.4S, V2.4S, V3.4S encodes register fields correctly

- FCMGT V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: FCMGT V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGT V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: FCMGT V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x6EA0E400 | (3 << 16) | (2 << 5) | 1
#      = 0x6EA0E400 | 0x30000 | 0x40 | 1
#      = 0x6EA3E441
# LE: 0x41, 0xE4, 0xA3, 0x6E
var b = emit_fcmgt_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_fcmgt_4s always returns 4 bytes

- emit_fcmgt_4s always returns 4 bytes
- Verify: emit_fcmgt_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcmgt_4s always returns 4 bytes")
step("Verify: emit_fcmgt_4s always returns 4 bytes")
var b = emit_fcmgt_4s(19, 20, 21)
expect(b.len()).to_equal(4)
```

</details>

### emit_fcmge_4s — fp compare greater-than-or-equal 4x32-bit lanes

#### FCMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- FCMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: FCMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: FCMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_fcmge_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x6E)
```

</details>

#### FCMGE V1.4S, V2.4S, V3.4S encodes register fields correctly

- FCMGE V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: FCMGE V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("FCMGE V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: FCMGE V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x6E20E400 | (3 << 16) | (2 << 5) | 1
#      = 0x6E20E400 | 0x30000 | 0x40 | 1
#      = 0x6E23E441
# LE: 0x41, 0xE4, 0x23, 0x6E
var b = emit_fcmge_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x23)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_fcmge_4s always returns 4 bytes

- emit_fcmge_4s always returns 4 bytes
- Verify: emit_fcmge_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_fcmge_4s always returns 4 bytes")
step("Verify: emit_fcmge_4s always returns 4 bytes")
var b = emit_fcmge_4s(22, 23, 24)
expect(b.len()).to_equal(4)
```

</details>

### emit_bsl_16b — bitwise select 128-bit

#### BSL V0.16B, V0.16B, V0.16B encodes to base opcode bytes

- BSL V0.16B, V0.16B, V0.16B encodes to base opcode bytes
- Verify: BSL V0.16B, V0.16B, V0.16B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x60`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
step("Verify: BSL V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
var b = emit_bsl_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x60)
expect(b[3]).to_equal(0x6E)
```

</details>

#### BSL V1.16B, V2.16B, V3.16B encodes register fields correctly

- BSL V1.16B, V2.16B, V3.16B encodes register fields correctly
- Verify: BSL V1.16B, V2.16B, V3.16B encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x63`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("BSL V1.16B, V2.16B, V3.16B encodes register fields correctly")
step("Verify: BSL V1.16B, V2.16B, V3.16B encodes register fields correctly")
# word = 0x6E601C00 | (3 << 16) | (2 << 5) | 1
#      = 0x6E601C00 | 0x30000 | 0x40 | 1
#      = 0x6E631C41
# LE: 0x41, 0x1C, 0x63, 0x6E
var b = emit_bsl_16b(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x63)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_bsl_16b always returns 4 bytes

- emit_bsl_16b always returns 4 bytes
- Verify: emit_bsl_16b always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_bsl_16b always returns 4 bytes")
step("Verify: emit_bsl_16b always returns 4 bytes")
var b = emit_bsl_16b(25, 26, 27)
expect(b.len()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-EMIT-CMEQ-4S-COMPARE-EQUAL-4X32-BIT-LANE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `064a86265f8886cabfcfdb2893e5ebc608b7ad66c4b6b422f0b92f8a2091327c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `064a86265f8886cabfcfdb2893e5ebc608b7ad66c4b6b422f0b92f8a2091327c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `064a86265f8886cabfcfdb2893e5ebc608b7ad66c4b6b422f0b92f8a2091327c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_cmp_emit_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_cmp_emit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_cmp_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_cmp_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_cmp_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_cmp_emit_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_cmp_emit_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_cmp_emit_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_cmeq_4s always returns 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
