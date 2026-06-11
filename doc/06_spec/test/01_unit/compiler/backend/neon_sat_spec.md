# Neon Sat Specification

> 1. var b = emit neon sqadd 4s

<!-- sdn-diagram:id=neon_sat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_sat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_sat_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_sat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Sat Specification

## Scenarios

### emit_neon_sqadd_4s — signed saturating add 4 lanes

#### SQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit neon sqadd 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_sqadd_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### SQADD V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit neon sqadd 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x4EA00C00 + 3*65536 + 2*32 + 1 = 0x4EA30C41
# LE bytes: 0x41, 0x0C, 0xA3, 0x4E
var b = emit_neon_sqadd_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_neon_uqadd_4s — unsigned saturating add 4 lanes

#### UQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit neon uqadd 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_uqadd_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### UQADD V5.4S, V6.4S, V7.4S encodes register fields correctly

1. var b = emit neon uqadd 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA7`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x6EA00C00 + 7*65536 + 6*32 + 5 = 0x6EA70CC5
# LE bytes: 0xC5, 0x0C, 0xA7, 0x6E
var b = emit_neon_uqadd_4s(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA7)
expect(b[3]).to_equal(0x6E)
```

</details>

### emit_neon_sqsub_4s — signed saturating subtract 4 lanes

#### SQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit neon sqsub 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_sqsub_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### SQSUB V1.4S, V2.4S, V3.4S encodes register fields correctly

1. var b = emit neon sqsub 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x4EA02C00 + 3*65536 + 2*32 + 1 = 0x4EA32C41
# LE bytes: 0x41, 0x2C, 0xA3, 0x4E
var b = emit_neon_sqsub_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_neon_uqsub_4s — unsigned saturating subtract 4 lanes

#### UQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes

1. var b = emit neon uqsub 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_uqsub_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### UQSUB V5.4S, V6.4S, V7.4S encodes register fields correctly

1. var b = emit neon uqsub 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA7`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x6EA02C00 + 7*65536 + 6*32 + 5 = 0x6EA72CC5
# LE bytes: 0xC5, 0x2C, 0xA7, 0x6E
var b = emit_neon_uqsub_4s(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA7)
expect(b[3]).to_equal(0x6E)
```

</details>

### SQADD/UQADD/SQSUB/UQSUB emit output length

#### emit_neon_sqadd_4s always returns 4 bytes

1. var b = emit neon sqadd 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_sqadd_4s(1, 2, 3)
expect(b.len()).to_equal(4)
```

</details>

#### emit_neon_uqsub_4s always returns 4 bytes

1. var b = emit neon uqsub 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_uqsub_4s(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### signed vs unsigned byte[3] distinction

#### SQADD and UQADD with same registers match bytes 0-2 and differ at byte[3]

1. var s = emit neon sqadd 4s
2. var u = emit neon uqadd 4s
   - Expected: s[0] equals `u[0]`
   - Expected: s[1] equals `u[1]`
   - Expected: s[2] equals `u[2]`
   - Expected: u[3] - s[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = emit_neon_sqadd_4s(1, 2, 3)
var u = emit_neon_uqadd_4s(1, 2, 3)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# UQADD has U=1 (bit 29), which raises byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
```

</details>

#### SQSUB and UQSUB with same registers match bytes 0-2 and differ at byte[3]

1. var s = emit neon sqsub 4s
2. var u = emit neon uqsub 4s
   - Expected: s[0] equals `u[0]`
   - Expected: s[1] equals `u[1]`
   - Expected: s[2] equals `u[2]`
   - Expected: u[3] - s[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = emit_neon_sqsub_4s(1, 2, 3)
var u = emit_neon_uqsub_4s(1, 2, 3)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# UQSUB has U=1 (bit 29), which raises byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_sat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_neon_sqadd_4s — signed saturating add 4 lanes
- emit_neon_uqadd_4s — unsigned saturating add 4 lanes
- emit_neon_sqsub_4s — signed saturating subtract 4 lanes
- emit_neon_uqsub_4s — unsigned saturating subtract 4 lanes
- SQADD/UQADD/SQSUB/UQSUB emit output length
- signed vs unsigned byte[3] distinction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
