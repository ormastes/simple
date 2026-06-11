# Neon Int Emit Specification

> 1. var b = emit addv 4s

<!-- sdn-diagram:id=neon_int_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_int_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_int_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_int_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Int Emit Specification

## Scenarios

### emit_addv_4s — integer add 4x32-bit lanes

#### ADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit addv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_addv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### ADD V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit addv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit addv 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_addv_4s(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### emit_subv_4s — integer subtract 4x32-bit lanes

#### SUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit subv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_subv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### SUB V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit subv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x84`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit subv 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_subv_4s(4, 5, 6)
expect(b.len()).to_equal(4)
```

</details>

### emit_mulv_4s — integer multiply 4x32-bit lanes

#### MUL V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit mulv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x9C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_mulv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x9C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### MUL V2.4S, V3.4S, V4.4S encodes register fields correctly

1. var b = emit mulv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x62`
   - Expected: b[1] equals `0x9C`
   - Expected: b[2] equals `0xA4`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit mulv 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_mulv_4s(7, 8, 9)
expect(b.len()).to_equal(4)
```

</details>

### emit_andv_16b — bitwise AND 128-bit

#### AND V0.16B, V0.16B, V0.16B encodes to base opcode bytes

1. var b = emit andv 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_andv_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x4E)
```

</details>

#### AND V1.16B, V2.16B, V3.16B encodes register fields correctly

1. var b = emit andv 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit andv 16b
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_andv_16b(3, 4, 5)
expect(b.len()).to_equal(4)
```

</details>

### emit_orrv_16b — bitwise OR 128-bit

#### ORR V0.16B, V0.16B, V0.16B encodes to base opcode bytes

1. var b = emit orrv 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_orrv_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### ORR V1.16B, V2.16B, V3.16B encodes register fields correctly

1. var b = emit orrv 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit orrv 16b
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_orrv_16b(6, 7, 8)
expect(b.len()).to_equal(4)
```

</details>

### emit_eorv_16b — bitwise XOR 128-bit

#### EOR V0.16B, V0.16B, V0.16B encodes to base opcode bytes

1. var b = emit eorv 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_eorv_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x6E)
```

</details>

#### EOR V1.16B, V2.16B, V3.16B encodes register fields correctly

1. var b = emit eorv 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit eorv 16b
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_eorv_16b(9, 10, 11)
expect(b.len()).to_equal(4)
```

</details>

### emit_shlv_4s — left shift immediate 4x32-bit lanes

#### SHL V0.4S, V0.4S, #0 encodes to base opcode bytes

1. var b = emit shlv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_shlv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x54)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x4F)
```

</details>

#### SHL V0.4S, V0.4S, #1 encodes imm=1 in bits[20:16]

1. var b = emit shlv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit shlv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0x24`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit shlv 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_shlv_4s(3, 4, 8)
expect(b.len()).to_equal(4)
```

</details>

### emit_sshrv_4s — signed right shift immediate 4x32-bit lanes

#### SSHR V0.4S, V0.4S, #32 encodes max shift (imm=32, bits[20:16]=0)

1. var b = emit sshrv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit sshrv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0x3F`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit sshrv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x04`
   - Expected: b[2] equals `0x3C`
   - Expected: b[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit sshrv 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_sshrv_4s(5, 6, 8)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmpeqv_4s — compare equal 4x32-bit lanes

#### CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit cmpeqv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x8C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmpeqv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x8C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit cmpeqv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x8C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit cmpeqv 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmpeqv_4s(4, 5, 6)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmgtv_4s — compare signed greater-than 4x32-bit lanes

#### CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit cmgtv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmgtv_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit cmgtv 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit cmgtv 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmgtv_4s(7, 8, 9)
expect(b.len()).to_equal(4)
```

</details>

### ADD vs SUB U-bit distinction

#### ADD and SUB with same regs match bytes 0-2 and differ at byte[3] by U-bit (0x20)

1. var a = emit addv 4s
2. var s = emit subv 4s
   - Expected: a[0] equals `s[0]`
   - Expected: a[1] equals `s[1]`
   - Expected: a[2] equals `s[2]`
   - Expected: s[3] - a[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var a = emit andv 16b
2. var e = emit eorv 16b
   - Expected: a[0] equals `e[0]`
   - Expected: a[1] equals `e[1]`
   - Expected: a[2] equals `e[2]`
   - Expected: e[3] - a[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var sh = emit shlv 4s
2. var ss = emit sshrv 4s
   - Expected: sh[3] equals `0x4F`
   - Expected: ss[3] equals `0x4F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sh = emit_shlv_4s(0, 0, 0)
var ss = emit_sshrv_4s(0, 0, 32)
expect(sh[3]).to_equal(0x4F)
expect(ss[3]).to_equal(0x4F)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_int_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_addv_4s — integer add 4x32-bit lanes
- emit_subv_4s — integer subtract 4x32-bit lanes
- emit_mulv_4s — integer multiply 4x32-bit lanes
- emit_andv_16b — bitwise AND 128-bit
- emit_orrv_16b — bitwise OR 128-bit
- emit_eorv_16b — bitwise XOR 128-bit
- emit_shlv_4s — left shift immediate 4x32-bit lanes
- emit_sshrv_4s — signed right shift immediate 4x32-bit lanes
- emit_cmpeqv_4s — compare equal 4x32-bit lanes
- emit_cmgtv_4s — compare signed greater-than 4x32-bit lanes
- ADD vs SUB U-bit distinction
- AND vs EOR U-bit distinction
- SHL vs SSHR base opcode byte consistency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
