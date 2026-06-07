# Neon Fp16 Specification

> 1. var b = emit fcvtn 4h

<!-- sdn-diagram:id=neon_fp16_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_fp16_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_fp16_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_fp16_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Fp16 Specification

## Scenarios

### emit_fcvtn_4h — narrow fp32 to fp16 into lower half

#### FCVTN V0.4H, V0.4S encodes to base opcode bytes

1. var b = emit fcvtn 4h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtn 4h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtn 4h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtn2 8h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtn2 8h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtn2 8h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x83`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtl 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtl 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtl 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x62`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtl2 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtl2 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtl2 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x62`
   - Expected: b[1] equals `0x78`
   - Expected: b[2] equals `0x21`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtzs 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtzs 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtzs 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x83`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtzu 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtzu 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x20`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtzu 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x83`
   - Expected: b[1] equals `0xB8`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var b = emit fcvtn 4h
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcvtn_4h(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtn2_8h always returns 4 bytes

1. var b = emit fcvtn2 8h
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcvtn2_8h(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtl_4s always returns 4 bytes

1. var b = emit fcvtl 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcvtl_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtl2_4s always returns 4 bytes

1. var b = emit fcvtl2 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcvtl2_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtzs_4s always returns 4 bytes

1. var b = emit fcvtzs 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcvtzs_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

#### emit_fcvtzu_4s always returns 4 bytes

1. var b = emit fcvtzu 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_fcvtzu_4s(1, 2)
expect(b.len()).to_equal(4)
```

</details>

### FCVTN vs FCVTN2 Q-bit distinction

#### FCVTN and FCVTN2 with same registers match bytes 0-2 and differ at byte[3]

1. var n  = emit fcvtn 4h
2. var n2 = emit fcvtn2 8h
   - Expected: n[0] equals `n2[0]`
   - Expected: n[1] equals `n2[1]`
   - Expected: n[2] equals `n2[2]`
   - Expected: n2[3] - n[3] equals `0x40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var s = emit fcvtzs 4s
2. var u = emit fcvtzu 4s
   - Expected: s[0] equals `u[0]`
   - Expected: s[1] equals `u[1]`
   - Expected: s[2] equals `u[2]`
   - Expected: u[3] - s[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = emit_fcvtzs_4s(0, 1)
var u = emit_fcvtzu_4s(0, 1)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# FCVTZU has U=1 (bit 29), raising byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_fp16_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_fcvtn_4h — narrow fp32 to fp16 into lower half
- emit_fcvtn2_8h — narrow fp32 to fp16 into upper half
- emit_fcvtl_4s — widen fp16 to fp32 from lower half
- emit_fcvtl2_4s — widen fp16 to fp32 from upper half
- emit_fcvtzs_4s — fp32 to signed int32 truncate 4 lanes
- emit_fcvtzu_4s — fp32 to unsigned int32 truncate 4 lanes
- FP16 conversion emit output length
- FCVTN vs FCVTN2 Q-bit distinction
- FCVTZS vs FCVTZU U-bit distinction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
