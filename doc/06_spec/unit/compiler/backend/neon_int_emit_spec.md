# neon_int_emit_spec

> Purpose: Prove that emit_addv_4s — integer add 4x32-bit lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_int_emit_spec

Purpose: Prove that emit_addv_4s — integer add 4x32-bit lanes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/neon_int_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_addv_4s — integer add 4x32-bit lanes.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_addv_4s — integer add 4x32-bit lanes

#### ADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: ADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: ADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
# @req: REQ-COMP-EMIT-ADDV-4S-INTEGER-ADD-4X32-BIT-LANES-001
var b = emit_addv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### ADD V1.4S, V2.4S, V3.4S encodes register fields correctly

- ADD V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: ADD V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADD V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: ADD V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x4EA08400 | (3 << 16) | (2 << 5) | 1
#      = 0x4EA08400 | 0x30000 | 0x40 | 1
#      = 0x4EA38441
# LE bytes: 0x41, 0x84, 0xA3, 0x4E
var b = emit_addv_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_addv_4s always returns 4 bytes

- emit_addv_4s always returns 4 bytes
- Verify: emit_addv_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_addv_4s always returns 4 bytes")
step("Verify: emit_addv_4s always returns 4 bytes")
var b = emit_addv_4s(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### emit_subv_4s — integer subtract 4x32-bit lanes

#### SUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- SUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: SUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: SUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_subv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### SUB V1.4S, V2.4S, V3.4S encodes register fields correctly

- SUB V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: SUB V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SUB V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: SUB V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x6EA08400 | (3 << 16) | (2 << 5) | 1 = 0x6EA38441
# LE bytes: 0x41, 0x84, 0xA3, 0x6E
var b = emit_subv_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_subv_4s always returns 4 bytes

- emit_subv_4s always returns 4 bytes
- Verify: emit_subv_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_subv_4s always returns 4 bytes")
step("Verify: emit_subv_4s always returns 4 bytes")
var b = emit_subv_4s(4, 5, 6)
expect(b.len()).to_equal(4)
```

</details>

### emit_mulv_4s — integer multiply 4x32-bit lanes

#### MUL V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- MUL V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: MUL V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x9C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MUL V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: MUL V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_mulv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x9C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### MUL V2.4S, V3.4S, V4.4S encodes register fields correctly

- MUL V2.4S, V3.4S, V4.4S encodes register fields correctly
- Verify: MUL V2.4S, V3.4S, V4.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x62`
   - Expected: b[1] equals `0x9C`
   - Expected: b[2] equals `0xA4`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MUL V2.4S, V3.4S, V4.4S encodes register fields correctly")
step("Verify: MUL V2.4S, V3.4S, V4.4S encodes register fields correctly")
# word = 0x4EA09C00 | (4 << 16) | (3 << 5) | 2
#      = 0x4EA09C00 | 0x40000 | 0x60 | 2
#      = 0x4EA49C62
# LE bytes: 0x62, 0x9C, 0xA4, 0x4E
var b = emit_mulv_4s(2, 3, 4)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x62)
expect(b[1]).to_equal(0x9C)
expect(b[2]).to_equal(0xA4)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_mulv_4s always returns 4 bytes

- emit_mulv_4s always returns 4 bytes
- Verify: emit_mulv_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_mulv_4s always returns 4 bytes")
step("Verify: emit_mulv_4s always returns 4 bytes")
var b = emit_mulv_4s(7, 8, 9)
expect(b.len()).to_equal(4)
```

</details>

### emit_andv_16b — bitwise AND 128-bit

#### AND V0.16B, V0.16B, V0.16B encodes to base opcode bytes

- AND V0.16B, V0.16B, V0.16B encodes to base opcode bytes
- Verify: AND V0.16B, V0.16B, V0.16B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AND V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
step("Verify: AND V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
var b = emit_andv_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x4E)
```

</details>

#### AND V1.16B, V2.16B, V3.16B encodes register fields correctly

- AND V1.16B, V2.16B, V3.16B encodes register fields correctly
- Verify: AND V1.16B, V2.16B, V3.16B encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AND V1.16B, V2.16B, V3.16B encodes register fields correctly")
step("Verify: AND V1.16B, V2.16B, V3.16B encodes register fields correctly")
# word = 0x4E201C00 | (3 << 16) | (2 << 5) | 1
#      = 0x4E201C00 | 0x30000 | 0x40 | 1
#      = 0x4E231C41
# LE bytes: 0x41, 0x1C, 0x23, 0x4E
var b = emit_andv_16b(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x23)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_andv_16b always returns 4 bytes

- emit_andv_16b always returns 4 bytes
- Verify: emit_andv_16b always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_andv_16b always returns 4 bytes")
step("Verify: emit_andv_16b always returns 4 bytes")
var b = emit_andv_16b(3, 4, 5)
expect(b.len()).to_equal(4)
```

</details>

### emit_orrv_16b — bitwise OR 128-bit

#### ORR V0.16B, V0.16B, V0.16B encodes to base opcode bytes

- ORR V0.16B, V0.16B, V0.16B encodes to base opcode bytes
- Verify: ORR V0.16B, V0.16B, V0.16B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ORR V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
step("Verify: ORR V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
var b = emit_orrv_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### ORR V1.16B, V2.16B, V3.16B encodes register fields correctly

- ORR V1.16B, V2.16B, V3.16B encodes register fields correctly
- Verify: ORR V1.16B, V2.16B, V3.16B encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ORR V1.16B, V2.16B, V3.16B encodes register fields correctly")
step("Verify: ORR V1.16B, V2.16B, V3.16B encodes register fields correctly")
# word = 0x4EA01C00 | (3 << 16) | (2 << 5) | 1
#      = 0x4EA01C00 | 0x30000 | 0x40 | 1
#      = 0x4EA31C41
# LE bytes: 0x41, 0x1C, 0xA3, 0x4E
var b = emit_orrv_16b(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_orrv_16b always returns 4 bytes

- emit_orrv_16b always returns 4 bytes
- Verify: emit_orrv_16b always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_orrv_16b always returns 4 bytes")
step("Verify: emit_orrv_16b always returns 4 bytes")
var b = emit_orrv_16b(6, 7, 8)
expect(b.len()).to_equal(4)
```

</details>

### emit_eorv_16b — bitwise XOR 128-bit

#### EOR V0.16B, V0.16B, V0.16B encodes to base opcode bytes

- EOR V0.16B, V0.16B, V0.16B encodes to base opcode bytes
- Verify: EOR V0.16B, V0.16B, V0.16B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EOR V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
step("Verify: EOR V0.16B, V0.16B, V0.16B encodes to base opcode bytes")
var b = emit_eorv_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x6E)
```

</details>

#### EOR V1.16B, V2.16B, V3.16B encodes register fields correctly

- EOR V1.16B, V2.16B, V3.16B encodes register fields correctly
- Verify: EOR V1.16B, V2.16B, V3.16B encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EOR V1.16B, V2.16B, V3.16B encodes register fields correctly")
step("Verify: EOR V1.16B, V2.16B, V3.16B encodes register fields correctly")
# word = 0x6E201C00 | (3 << 16) | (2 << 5) | 1
#      = 0x6E201C00 | 0x30000 | 0x40 | 1
#      = 0x6E231C41
# LE bytes: 0x41, 0x1C, 0x23, 0x6E
var b = emit_eorv_16b(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x23)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_eorv_16b always returns 4 bytes

- emit_eorv_16b always returns 4 bytes
- Verify: emit_eorv_16b always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_eorv_16b always returns 4 bytes")
step("Verify: emit_eorv_16b always returns 4 bytes")
var b = emit_eorv_16b(9, 10, 11)
expect(b.len()).to_equal(4)
```

</details>

### emit_shlv_4s — left shift immediate 4x32-bit lanes

#### SHL V0.4S, V0.4S, #0 encodes to base opcode bytes

- SHL V0.4S, V0.4S, #0 encodes to base opcode bytes
- Verify: SHL V0.4S, V0.4S, #0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHL V0.4S, V0.4S, #0 encodes to base opcode bytes")
step("Verify: SHL V0.4S, V0.4S, #0 encodes to base opcode bytes")
var b = emit_shlv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x54)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x4F)
```

</details>

#### SHL V0.4S, V0.4S, #1 encodes imm=1 in bits[20:16]

- SHL V0.4S, V0.4S, #1 encodes imm=1 in bits[20:16]
- Verify: SHL V0.4S, V0.4S, #1 encodes imm=1 in bits[20:16]
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHL V0.4S, V0.4S, #1 encodes imm=1 in bits[20:16]")
step("Verify: SHL V0.4S, V0.4S, #1 encodes imm=1 in bits[20:16]")
# word = 0x4F205400 | (1 << 16) = 0x4F215400
# LE: 0x00, 0x54, 0x21, 0x4F
var b = emit_shlv_4s(0, 0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x54)
expect(b[2]).to_equal(0x21)
expect(b[3]).to_equal(0x4F)
```

</details>

#### SHL V1.4S, V2.4S, #4 encodes register and imm correctly

- SHL V1.4S, V2.4S, #4 encodes register and imm correctly
- Verify: SHL V1.4S, V2.4S, #4 encodes register and imm correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0x24`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHL V1.4S, V2.4S, #4 encodes register and imm correctly")
step("Verify: SHL V1.4S, V2.4S, #4 encodes register and imm correctly")
# word = 0x4F205400 | (4 << 16) | (2 << 5) | 1
#      = 0x4F205400 | 0x40000 | 0x40 | 1
#      = 0x4F245441
# LE: 0x41, 0x54, 0x24, 0x4F
var b = emit_shlv_4s(1, 2, 4)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x54)
expect(b[2]).to_equal(0x24)
expect(b[3]).to_equal(0x4F)
```

</details>

#### emit_shlv_4s always returns 4 bytes

- emit_shlv_4s always returns 4 bytes
- Verify: emit_shlv_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_shlv_4s always returns 4 bytes")
step("Verify: emit_shlv_4s always returns 4 bytes")
var b = emit_shlv_4s(3, 4, 8)
expect(b.len()).to_equal(4)
```

</details>

### emit_sshrv_4s — signed right shift immediate 4x32-bit lanes

#### SSHR V0.4S, V0.4S, #32 encodes max shift (imm=32, bits[20:16]=0)

- SSHR V0.4S, V0.4S, #32 encodes max shift (imm=32, bits[20:16]=0)
- Verify: SSHR V0.4S, V0.4S, #32 encodes max shift (imm=32, bits[20:16]=0)
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SSHR V0.4S, V0.4S, #32 encodes max shift (imm=32, bits[20:16]=0)")
step("Verify: SSHR V0.4S, V0.4S, #32 encodes max shift (imm=32, bits[20:16]=0)")
# (32 - 32) & 0x1F = 0 => word = 0x4F200400
# LE: 0x00, 0x04, 0x20, 0x4F
var b = emit_sshrv_4s(0, 0, 32)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x4F)
```

</details>

#### SSHR V0.4S, V0.4S, #1 encodes imm=1 (bits[20:16]=31=0x1F)

- SSHR V0.4S, V0.4S, #1 encodes imm=1 (bits[20:16]=31=0x1F)
- Verify: SSHR V0.4S, V0.4S, #1 encodes imm=1 (bits[20:16]=31=0x1F)
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0x3F`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SSHR V0.4S, V0.4S, #1 encodes imm=1 (bits[20:16]=31=0x1F)")
step("Verify: SSHR V0.4S, V0.4S, #1 encodes imm=1 (bits[20:16]=31=0x1F)")
# (32 - 1) & 0x1F = 31 = 0x1F => word = 0x4F200400 | (0x1F << 16) = 0x4F3F0400
# LE: 0x00, 0x04, 0x3F, 0x4F
var b = emit_sshrv_4s(0, 0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0x3F)
expect(b[3]).to_equal(0x4F)
```

</details>

#### SSHR V1.4S, V2.4S, #4 encodes register and imm correctly

- SSHR V1.4S, V2.4S, #4 encodes register and imm correctly
- Verify: SSHR V1.4S, V2.4S, #4 encodes register and imm correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0x3C`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SSHR V1.4S, V2.4S, #4 encodes register and imm correctly")
step("Verify: SSHR V1.4S, V2.4S, #4 encodes register and imm correctly")
# (32 - 4) & 0x1F = 28 = 0x1C => word = 0x4F200400 | (0x1C << 16) | (2 << 5) | 1
#      = 0x4F200400 | 0x1C0000 | 0x40 | 1
#      = 0x4F3C0441
# LE: 0x41, 0x04, 0x3C, 0x4F
var b = emit_sshrv_4s(1, 2, 4)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0x3C)
expect(b[3]).to_equal(0x4F)
```

</details>

#### emit_sshrv_4s always returns 4 bytes

- emit_sshrv_4s always returns 4 bytes
- Verify: emit_sshrv_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_sshrv_4s always returns 4 bytes")
step("Verify: emit_sshrv_4s always returns 4 bytes")
var b = emit_sshrv_4s(5, 6, 8)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmpeqv_4s — compare equal 4x32-bit lanes

#### CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x8C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_cmpeqv_4s(0, 0, 0)
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
# @req REQ-SSPEC-UNIT
step("CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x6EA08C00 | (3 << 16) | (2 << 5) | 1
#      = 0x6EA08C00 | 0x30000 | 0x40 | 1
#      = 0x6EA38C41
# LE: 0x41, 0x8C, 0xA3, 0x6E
var b = emit_cmpeqv_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x8C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_cmpeqv_4s always returns 4 bytes

- emit_cmpeqv_4s always returns 4 bytes
- Verify: emit_cmpeqv_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_cmpeqv_4s always returns 4 bytes")
step("Verify: emit_cmpeqv_4s always returns 4 bytes")
var b = emit_cmpeqv_4s(4, 5, 6)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmgtv_4s — compare signed greater-than 4x32-bit lanes

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
# @req REQ-SSPEC-UNIT
step("CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_cmgtv_4s(0, 0, 0)
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
# @req REQ-SSPEC-UNIT
step("CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x4EA03400 | (3 << 16) | (2 << 5) | 1
#      = 0x4EA03400 | 0x30000 | 0x40 | 1
#      = 0x4EA33441
# LE: 0x41, 0x34, 0xA3, 0x4E
var b = emit_cmgtv_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_cmgtv_4s always returns 4 bytes

- emit_cmgtv_4s always returns 4 bytes
- Verify: emit_cmgtv_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_cmgtv_4s always returns 4 bytes")
step("Verify: emit_cmgtv_4s always returns 4 bytes")
var b = emit_cmgtv_4s(7, 8, 9)
expect(b.len()).to_equal(4)
```

</details>

### ADD vs SUB U-bit distinction

#### ADD and SUB with same regs match bytes 0-2 and differ at byte[3] by U-bit (0x20)

- ADD and SUB with same regs match bytes 0-2 and differ at byte[3] by U-bit (0x20)
- Verify: ADD and SUB with same regs match bytes 0-2 and differ at byte[3] by U-bit (0x20)
   - Expected: a[0] equals `s[0]`
   - Expected: a[1] equals `s[1]`
   - Expected: a[2] equals `s[2]`
   - Expected: s[3] - a[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ADD and SUB with same regs match bytes 0-2 and differ at byte[3] by U-bit (0x20)")
step("Verify: ADD and SUB with same regs match bytes 0-2 and differ at byte[3] by U-bit (0x20)")
# ADD base 0x4EA08400 vs SUB base 0x6EA08400: differ in bit 29 (byte[3] 0x4E vs 0x6E)
var a = emit_addv_4s(0, 0, 0)
var s = emit_subv_4s(0, 0, 0)
expect(a[0]).to_equal(s[0])
expect(a[1]).to_equal(s[1])
expect(a[2]).to_equal(s[2])
expect(s[3] - a[3]).to_equal(0x20)
```

</details>

### AND vs EOR U-bit distinction

#### AND (U=0) and EOR (U=1) with same regs differ at byte[3] by 0x20

- AND (U=0) and EOR (U=1) with same regs differ at byte[3] by 0x20
- Verify: AND (U=0) and EOR (U=1) with same regs differ at byte[3] by 0x20
   - Expected: a[0] equals `e[0]`
   - Expected: a[1] equals `e[1]`
   - Expected: a[2] equals `e[2]`
   - Expected: e[3] - a[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AND (U=0) and EOR (U=1) with same regs differ at byte[3] by 0x20")
step("Verify: AND (U=0) and EOR (U=1) with same regs differ at byte[3] by 0x20")
var a = emit_andv_16b(0, 0, 0)
var e = emit_eorv_16b(0, 0, 0)
expect(a[0]).to_equal(e[0])
expect(a[1]).to_equal(e[1])
expect(a[2]).to_equal(e[2])
expect(e[3] - a[3]).to_equal(0x20)
```

</details>

### SHL vs SSHR base opcode byte consistency

#### SHL and SSHR for same rd/rn share byte[3] = 0x4F

- SHL and SSHR for same rd/rn share byte[3] = 0x4F
- Verify: SHL and SSHR for same rd/rn share byte[3] = 0x4F
   - Expected: sh[3] equals `0x4F`
   - Expected: ss[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHL and SSHR for same rd/rn share byte[3] = 0x4F")
step("Verify: SHL and SSHR for same rd/rn share byte[3] = 0x4F")
var sh = emit_shlv_4s(0, 0, 0)
var ss = emit_sshrv_4s(0, 0, 32)
expect(sh[3]).to_equal(0x4F)
expect(ss[3]).to_equal(0x4F)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-EMIT-ADDV-4S-INTEGER-ADD-4X32-BIT-LANES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `418ae789f48fe6649eb41d07648d7a00316f24653edc356e953d006889198439`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `418ae789f48fe6649eb41d07648d7a00316f24653edc356e953d006889198439`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `418ae789f48fe6649eb41d07648d7a00316f24653edc356e953d006889198439`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/neon_int_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/neon_int_emit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/neon_int_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/neon_int_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/neon_int_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 32 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/neon_int_emit_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/neon_int_emit_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ADD V1.4S, V2.4S, V3.4S encodes register fields correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/neon_int_emit_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_addv_4s always returns 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
