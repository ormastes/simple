# Neon Cmp Emit Specification

> 1. var b = emit cmeq 4s

<!-- sdn-diagram:id=neon_cmp_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_cmp_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_cmp_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_cmp_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Cmp Emit Specification

## Scenarios

### emit_cmeq_4s — compare equal 4x32-bit lanes

#### CMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit cmeq 4s
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
var b = emit_cmeq_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x8C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### CMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit cmeq 4s
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
var b = emit_cmeq_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x8C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_cmeq_4s always returns 4 bytes

1. var b = emit cmeq 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmeq_4s(4, 5, 6)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmgt_4s — compare signed greater-than 4x32-bit lanes

#### CMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit cmgt 4s
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
var b = emit_cmgt_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### CMGT V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit cmgt 4s
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
var b = emit_cmgt_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_cmgt_4s always returns 4 bytes

1. var b = emit cmgt 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmgt_4s(7, 8, 9)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmge_4s — compare signed greater-than-or-equal 4x32-bit lanes

#### CMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit cmge 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x3C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmge_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x3C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### CMGE V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit cmge 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x3C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit cmge 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmge_4s(10, 11, 12)
expect(b.len()).to_equal(4)
```

</details>

### emit_cmhi_4s — compare unsigned higher 4x32-bit lanes

#### CMHI V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit cmhi 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmhi_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x34)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### CMHI V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit cmhi 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x34`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit cmhi 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_cmhi_4s(13, 14, 15)
expect(b.len()).to_equal(4)
```

</details>

### emit_fcmeq_4s — fp compare equal 4x32-bit lanes

#### FCMEQ V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit fcmeq 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcmeq_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x4E)
```

</details>

#### FCMEQ V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit fcmeq 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcmeq 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcmeq_4s(16, 17, 18)
expect(b.len()).to_equal(4)
```

</details>

### emit_fcmgt_4s — fp compare greater-than 4x32-bit lanes

#### FCMGT V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit fcmgt 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcmgt_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### FCMGT V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit fcmgt 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcmgt 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcmgt_4s(19, 20, 21)
expect(b.len()).to_equal(4)
```

</details>

### emit_fcmge_4s — fp compare greater-than-or-equal 4x32-bit lanes

#### FCMGE V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit fcmge 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x20`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcmge_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x20)
expect(b[3]).to_equal(0x6E)
```

</details>

#### FCMGE V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit fcmge 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xE4`
   - Expected: b[2] equals `0x23`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcmge 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcmge_4s(22, 23, 24)
expect(b.len()).to_equal(4)
```

</details>

### emit_bsl_16b — bitwise select 128-bit

#### BSL V0.16B, V0.16B, V0.16B encodes to base opcode bytes

1. var b = emit bsl 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x60`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bsl_16b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x1C)
expect(b[2]).to_equal(0x60)
expect(b[3]).to_equal(0x6E)
```

</details>

#### BSL V1.16B, V2.16B, V3.16B encodes register fields correctly

1. var b = emit bsl 16b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x1C`
   - Expected: b[2] equals `0x63`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit bsl 16b
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bsl_16b(25, 26, 27)
expect(b.len()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_cmp_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_cmeq_4s — compare equal 4x32-bit lanes
- emit_cmgt_4s — compare signed greater-than 4x32-bit lanes
- emit_cmge_4s — compare signed greater-than-or-equal 4x32-bit lanes
- emit_cmhi_4s — compare unsigned higher 4x32-bit lanes
- emit_fcmeq_4s — fp compare equal 4x32-bit lanes
- emit_fcmgt_4s — fp compare greater-than 4x32-bit lanes
- emit_fcmge_4s — fp compare greater-than-or-equal 4x32-bit lanes
- emit_bsl_16b — bitwise select 128-bit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
