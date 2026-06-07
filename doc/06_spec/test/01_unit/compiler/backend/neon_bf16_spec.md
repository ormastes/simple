# Neon Bf16 Specification

> 1. var b = emit bfdot v4bf16

<!-- sdn-diagram:id=neon_bf16_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_bf16_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_bf16_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_bf16_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Bf16 Specification

## Scenarios

### emit_bfdot_v4bf16 — BF16 dot product 64-bit

#### BFDOT V0.2S, V0.4H, V0.4H encodes to base opcode bytes

1. var b = emit bfdot v4bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xFC`
   - Expected: b[2] equals `0x40`
   - Expected: b[3] equals `0x2E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfdot_v4bf16(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xFC)
expect(b[2]).to_equal(0x40)
expect(b[3]).to_equal(0x2E)
```

</details>

#### BFDOT V1.2S, V2.4H, V3.4H encodes register fields correctly

1. var b = emit bfdot v4bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xFC`
   - Expected: b[2] equals `0x43`
   - Expected: b[3] equals `0x2E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x2E40FC00 + 3*65536 + 2*32 + 1 = 0x2E43FC41
# LE bytes: 0x41, 0xFC, 0x43, 0x2E
var b = emit_bfdot_v4bf16(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0xFC)
expect(b[2]).to_equal(0x43)
expect(b[3]).to_equal(0x2E)
```

</details>

#### emit_bfdot_v4bf16 always returns 4 bytes

1. var b = emit bfdot v4bf16
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfdot_v4bf16(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### emit_bfmmla_v4bf16 — BF16 matrix multiply-accumulate 128-bit

#### BFMMLA V0.4S, V0.8H, V0.8H encodes to base opcode bytes

1. var b = emit bfmmla v4bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xEC`
   - Expected: b[2] equals `0x40`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfmmla_v4bf16(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xEC)
expect(b[2]).to_equal(0x40)
expect(b[3]).to_equal(0x6E)
```

</details>

#### BFMMLA V1.4S, V2.8H, V3.8H encodes register fields correctly

1. var b = emit bfmmla v4bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xEC`
   - Expected: b[2] equals `0x43`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x6E40EC00 + 3*65536 + 2*32 + 1 = 0x6E43EC41
# LE bytes: 0x41, 0xEC, 0x43, 0x6E
var b = emit_bfmmla_v4bf16(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0xEC)
expect(b[2]).to_equal(0x43)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_bfmmla_v4bf16 always returns 4 bytes

1. var b = emit bfmmla v4bf16
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfmmla_v4bf16(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### emit_bfcvtn_v4bf16 — narrow float32 to bfloat16 lower half

#### BFCVTN V0.4H, V0.4S encodes to base opcode bytes

1. var b = emit bfcvtn v4bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfcvtn_v4bf16(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x0E)
```

</details>

#### BFCVTN V1.4H, V2.4S encodes register fields correctly

1. var b = emit bfcvtn v4bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x0EA16800 + 2*32 + 1 = 0x0EA16841
# LE bytes: 0x41, 0x68, 0xA1, 0x0E
var b = emit_bfcvtn_v4bf16(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x0E)
```

</details>

#### emit_bfcvtn_v4bf16 always returns 4 bytes

1. var b = emit bfcvtn v4bf16
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfcvtn_v4bf16(3, 4)
expect(b.len()).to_equal(4)
```

</details>

### emit_bfcvtn2_v8bf16 — narrow float32 to bfloat16 upper half

#### BFCVTN2 V0.8H, V0.4S encodes to base opcode bytes

1. var b = emit bfcvtn2 v8bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfcvtn2_v8bf16(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x4E)
```

</details>

#### BFCVTN2 V1.8H, V2.4S encodes register fields correctly

1. var b = emit bfcvtn2 v8bf16
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x4EA16800 + 2*32 + 1 = 0x4EA16841
# LE bytes: 0x41, 0x68, 0xA1, 0x4E
var b = emit_bfcvtn2_v8bf16(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_bfcvtn2_v8bf16 always returns 4 bytes

1. var b = emit bfcvtn2 v8bf16
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_bfcvtn2_v8bf16(3, 4)
expect(b.len()).to_equal(4)
```

</details>

### BFCVTN vs BFCVTN2 Q-bit distinction

#### BFCVTN and BFCVTN2 with same regs match bytes 0-2 and differ at byte[3]

1. var n = emit bfcvtn v4bf16
2. var n2 = emit bfcvtn2 v8bf16
   - Expected: n[0] equals `n2[0]`
   - Expected: n[1] equals `n2[1]`
   - Expected: n[2] equals `n2[2]`
   - Expected: n2[3] - n[3] equals `0x40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var n = emit_bfcvtn_v4bf16(1, 2)
var n2 = emit_bfcvtn2_v8bf16(1, 2)
expect(n[0]).to_equal(n2[0])
expect(n[1]).to_equal(n2[1])
expect(n[2]).to_equal(n2[2])
# BFCVTN2 has Q=1 (bit 30), which raises byte[3] by 0x40
expect(n2[3] - n[3]).to_equal(0x40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_bf16_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_bfdot_v4bf16 — BF16 dot product 64-bit
- emit_bfmmla_v4bf16 — BF16 matrix multiply-accumulate 128-bit
- emit_bfcvtn_v4bf16 — narrow float32 to bfloat16 lower half
- emit_bfcvtn2_v8bf16 — narrow float32 to bfloat16 upper half
- BFCVTN vs BFCVTN2 Q-bit distinction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
