# Neon Crc32 Specification

> 1. var b = emit neon crc32b

<!-- sdn-diagram:id=neon_crc32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=neon_crc32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

neon_crc32_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=neon_crc32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Neon Crc32 Specification

## Scenarios

### emit_neon_crc32b — CRC-32 byte accumulate

#### CRC32B W0, W0, W0 encodes to base opcode bytes

1. var b = emit neon crc32b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

#### CRC32B W1, W2, W3 encodes register fields correctly

1. var b = emit neon crc32b
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0xC3`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x1AC04000 + 3*65536 + 2*32 + 1 = 0x1AC34041
# LE bytes: 0x41, 0x40, 0xC3, 0x1A
var b = emit_neon_crc32b(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0xC3)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32h — CRC-32 halfword accumulate

#### CRC32H W0, W0, W0 encodes to base opcode bytes

1. var b = emit neon crc32h
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x44`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32h(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32w — CRC-32 word accumulate

#### CRC32W W0, W0, W0 encodes to base opcode bytes

1. var b = emit neon crc32w
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32w(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

#### CRC32W W0, W0, W1 encodes Rm=1 correctly

1. var b = emit neon crc32w
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0xC1`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32w(0, 0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0xC1)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32x — CRC-32 doubleword accumulate

#### CRC32X W0, W0, X0 encodes to base opcode bytes

1. var b = emit neon crc32x
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x4C`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32x(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x4C)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x9A)
```

</details>

### emit_neon_crc32cb — CRC-32C byte accumulate

#### CRC32CB W0, W0, W0 encodes to base opcode bytes

1. var b = emit neon crc32cb
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x50`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32cb(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x50)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32ch — CRC-32C halfword accumulate

#### CRC32CH W0, W0, W0 encodes to base opcode bytes

1. var b = emit neon crc32ch
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32ch(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x54)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32cw — CRC-32C word accumulate

#### CRC32CW W0, W0, W0 encodes to base opcode bytes

1. var b = emit neon crc32cw
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x58`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32cw(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x58)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32cx — CRC-32C doubleword accumulate

#### CRC32CX W0, W0, X0 encodes to base opcode bytes

1. var b = emit neon crc32cx
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x5C`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = emit_neon_crc32cx(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x9A)
```

</details>

#### CRC32CX W5, W6, X7 encodes register fields correctly

1. var b = emit neon crc32cx
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x5C`
   - Expected: b[2] equals `0xC7`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0x9AC05C00 + 7*65536 + 6*32 + 5 = 0x9AC75CC5
# LE bytes: 0xC5, 0x5C, 0xC7, 0x9A
var b = emit_neon_crc32cx(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0xC7)
expect(b[3]).to_equal(0x9A)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_crc32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- emit_neon_crc32b — CRC-32 byte accumulate
- emit_neon_crc32h — CRC-32 halfword accumulate
- emit_neon_crc32w — CRC-32 word accumulate
- emit_neon_crc32x — CRC-32 doubleword accumulate
- emit_neon_crc32cb — CRC-32C byte accumulate
- emit_neon_crc32ch — CRC-32C halfword accumulate
- emit_neon_crc32cw — CRC-32C word accumulate
- emit_neon_crc32cx — CRC-32C doubleword accumulate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
