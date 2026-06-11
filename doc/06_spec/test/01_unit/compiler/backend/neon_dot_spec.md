# Neon Dot Specification

> 1. var b = emit neon sdot 4s

<!-- sdn-diagram:id=neon_dot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_dot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_dot_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_dot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Dot Specification

## Scenarios

### emit_neon_sdot_4s — signed int8 dot product 4 lanes

#### SDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes

1. var b = emit neon sdot 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_sdot_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x4E)
```

</details>

#### SDOT V1.4S, V2.16B, V3.16B encodes register fields correctly

1. var b = emit neon sdot 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x83`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x4E809400 + 3*65536 + 2*32 + 1 = 0x4E839441
# LE bytes: 0x41, 0x94, 0x83, 0x4E
var b = emit_neon_sdot_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x83)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_neon_udot_4s — unsigned int8 dot product 4 lanes

#### UDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes

1. var b = emit neon udot 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_udot_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x6E)
```

</details>

#### UDOT V5.4S, V6.16B, V7.16B encodes register fields correctly

1. var b = emit neon udot 4s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x87`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x6E809400 + 7*65536 + 6*32 + 5 = 0x6E8794C5
# LE bytes: 0xC5, 0x94, 0x87, 0x6E
var b = emit_neon_udot_4s(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x87)
expect(b[3]).to_equal(0x6E)
```

</details>

### emit_neon_sdot_2s — signed int8 dot product 2 lanes

#### SDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes

1. var b = emit neon sdot 2s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_sdot_2s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x0E)
```

</details>

### emit_neon_udot_2s — unsigned int8 dot product 2 lanes

#### UDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes

1. var b = emit neon udot 2s
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x2E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_udot_2s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x2E)
```

</details>

### SDOT/UDOT emit output length

#### emit_neon_sdot_4s always returns 4 bytes

1. var b = emit neon sdot 4s
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_sdot_4s(1, 2, 3)
expect(b.len()).to_equal(4)
```

</details>

### SDOT vs UDOT byte[3] distinction

#### SDOT and UDOT 4S with same registers match bytes 0-2 and differ at byte[3]

1. var s = emit neon sdot 4s
2. var u = emit neon udot 4s
   - Expected: s[0] equals `u[0]`
   - Expected: s[1] equals `u[1]`
   - Expected: s[2] equals `u[2]`
   - Expected: u[3] - s[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = emit_neon_sdot_4s(1, 2, 3)
var u = emit_neon_udot_4s(1, 2, 3)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# UDOT has U=1 (bit 29), which raises byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_dot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_neon_sdot_4s — signed int8 dot product 4 lanes
- emit_neon_udot_4s — unsigned int8 dot product 4 lanes
- emit_neon_sdot_2s — signed int8 dot product 2 lanes
- emit_neon_udot_2s — unsigned int8 dot product 2 lanes
- SDOT/UDOT emit output length
- SDOT vs UDOT byte[3] distinction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
