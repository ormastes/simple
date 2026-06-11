# Sve2 Cmp Emit Specification

> <details>

<!-- sdn-diagram:id=sve2_cmp_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sve2_cmp_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sve2_cmp_emit_spec -> std
sve2_cmp_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sve2_cmp_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sve2 Cmp Emit Specification

## Scenarios

### SVE2 comparison/select emit golden bytes

### CMPEQ

#### cmpeq_s pd=0 pg=0 zn=0 zm=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmpeq_s(0, 0, 0, 0)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xA0)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x24)
```

</details>

#### cmpeq_s pd=1 pg=2 zn=3 zm=5

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmpeq_s(1, 2, 3, 5)
expect(b[0]).to_equal(0x61)
expect(b[1]).to_equal(0xA8)
expect(b[2]).to_equal(0x85)
expect(b[3]).to_equal(0x24)
```

</details>

### CMPGT

#### cmpgt_s pd=0 pg=1 zn=2 zm=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmpgt_s(0, 1, 2, 3)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x50)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0x83)
expect(b[3]).to_equal(0x24)
```

</details>

#### cmpgt_s pd=2 pg=3 zn=4 zm=7

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmpgt_s(2, 3, 4, 7)
expect(b[0]).to_equal(0x92)
expect(b[1]).to_equal(0x8C)
expect(b[2]).to_equal(0x87)
expect(b[3]).to_equal(0x24)
```

</details>

### CMPGE

#### cmpge_s pd=0 pg=1 zn=2 zm=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmpge_s(0, 1, 2, 3)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x40)
expect(b[1]).to_equal(0x84)
expect(b[2]).to_equal(0x83)
expect(b[3]).to_equal(0x24)
```

</details>

#### cmpge_s pd=3 pg=2 zn=5 zm=6

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmpge_s(3, 2, 5, 6)
expect(b[0]).to_equal(0xA3)
expect(b[1]).to_equal(0x88)
expect(b[2]).to_equal(0x86)
expect(b[3]).to_equal(0x24)
```

</details>

### CMPHI

#### cmphi_s pd=0 pg=1 zn=2 zm=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmphi_s(0, 1, 2, 3)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x50)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0x83)
expect(b[3]).to_equal(0x24)
```

</details>

#### cmphi_s pd=1 pg=0 zn=4 zm=7

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_cmphi_s(1, 0, 4, 7)
expect(b[0]).to_equal(0x91)
expect(b[1]).to_equal(0x00)
expect(b[2]).to_equal(0x87)
expect(b[3]).to_equal(0x24)
```

</details>

### CMPLO

#### cmplo_s pd=0 pg=1 zn=3 zm=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CMPLO(pd=0,pg=1,zn=3,zm=2) encodes as CMPHI with Zn/Zm swapped:
# CMPHI(zm=zn=3, zn=zm=2) = 0x24830450
val b = emit_cmplo_s(0, 1, 3, 2)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x50)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0x83)
expect(b[3]).to_equal(0x24)
```

</details>

#### cmplo_s pd=2 pg=0 zn=7 zm=4

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# CMPLO(pd=2,pg=0,zn=7,zm=4) -> CMPHI(zm=7,zn=4) = 0x24870092
val b = emit_cmplo_s(2, 0, 7, 4)
expect(b[0]).to_equal(0x92)
expect(b[1]).to_equal(0x00)
expect(b[2]).to_equal(0x87)
expect(b[3]).to_equal(0x24)
```

</details>

### SEL

#### sel_z_s zd=0 pg=0 zn=0 zm=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_sel_z_s(0, 0, 0, 0)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xC0)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x05)
```

</details>

#### sel_z_s zd=1 pg=2 zn=3 zm=5

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_sel_z_s(1, 2, 3, 5)
expect(b[0]).to_equal(0x61)
expect(b[1]).to_equal(0xC8)
expect(b[2]).to_equal(0xA5)
expect(b[3]).to_equal(0x05)
```

</details>

### COMPACT

#### compact_s zd=0 pg=0 zn=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_compact_s(0, 0, 0)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x80)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x05)
```

</details>

#### compact_s zd=1 pg=2 zn=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_compact_s(1, 2, 3)
expect(b[0]).to_equal(0x61)
expect(b[1]).to_equal(0x88)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x05)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/sve2_cmp_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SVE2 comparison/select emit golden bytes
- CMPEQ
- CMPGT
- CMPGE
- CMPHI
- CMPLO
- SEL
- COMPACT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
