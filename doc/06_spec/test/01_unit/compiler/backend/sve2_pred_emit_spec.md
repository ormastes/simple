# Sve2 Pred Emit Specification

> <details>

<!-- sdn-diagram:id=sve2_pred_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sve2_pred_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sve2_pred_emit_spec -> std
sve2_pred_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sve2_pred_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sve2 Pred Emit Specification

## Scenarios

### SVE2 predicate emit golden bytes

### PTRUE

#### ptrue_s pd=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_ptrue_s(0)
expect(b.length).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

#### ptrue_s pd=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_ptrue_s(3)
expect(b[0]).to_equal(0x03)
expect(b[1]).to_equal(0xE0)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

### PFALSE

#### pfalse pd=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_pfalse(0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

#### pfalse pd=7

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_pfalse(7)
expect(b[0]).to_equal(0x07)
expect(b[1]).to_equal(0xE4)
expect(b[2]).to_equal(0x18)
expect(b[3]).to_equal(0x25)
```

</details>

### WHILELT

#### whilelt_s pd=0 rn=0 rm=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_whilelt_s(0, 0, 0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x25)
```

</details>

#### whilelt_s pd=1 rn=2 rm=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_whilelt_s(1, 2, 3)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x04)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x25)
```

</details>

### WHILELE

#### whilele_s pd=2 rn=5 rm=10

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_whilele_s(2, 5, 10)
expect(b[0]).to_equal(0xA2)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xAA)
expect(b[3]).to_equal(0x25)
```

</details>

### AND predicate

#### and_pred pd=0 pg=1 pn=2 pm=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_and_pred(0, 1, 2, 3)
expect(b[0]).to_equal(0x40)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0x03)
expect(b[3]).to_equal(0x25)
```

</details>

#### and_pred pd=5 pg=7 pn=3 pm=15

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_and_pred(5, 7, 3, 15)
expect(b[0]).to_equal(0x65)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0x0F)
expect(b[3]).to_equal(0x25)
```

</details>

### ORR predicate

#### orr_pred pd=0 pg=0 pn=0 pm=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_orr_pred(0, 0, 0, 0)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x25)
```

</details>

#### orr_pred pd=1 pg=2 pn=3 pm=4

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_orr_pred(1, 2, 3, 4)
expect(b[0]).to_equal(0x61)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0x84)
expect(b[3]).to_equal(0x25)
```

</details>

### EOR predicate

#### eor_pred pd=0 pg=1 pn=2 pm=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_eor_pred(0, 1, 2, 3)
expect(b[0]).to_equal(0x40)
expect(b[1]).to_equal(0x46)
expect(b[2]).to_equal(0x03)
expect(b[3]).to_equal(0x25)
```

</details>

### NOT predicate

#### not_pred pd=0 pg=0 pn=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_not_pred(0, 0, 0)
expect(b[0]).to_equal(0x10)
expect(b[1]).to_equal(0x42)
expect(b[2]).to_equal(0x00)
expect(b[3]).to_equal(0x25)
```

</details>

#### not_pred pd=1 pg=2 pn=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_not_pred(1, 2, 3)
expect(b[0]).to_equal(0x71)
expect(b[1]).to_equal(0x4A)
expect(b[2]).to_equal(0x00)
expect(b[3]).to_equal(0x25)
```

</details>

### BRKA

#### brka pd=0 pg=1 pn=2

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_brka(0, 1, 2)
expect(b[0]).to_equal(0x40)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0x10)
expect(b[3]).to_equal(0x25)
```

</details>

#### brka pd=3 pg=7 pn=5

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_brka(3, 7, 5)
expect(b[0]).to_equal(0xA3)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0x10)
expect(b[3]).to_equal(0x25)
```

</details>

### PNEXT

#### pnext_s pd=0 pg=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_pnext_s(0, 1)
expect(b[0]).to_equal(0x20)
expect(b[1]).to_equal(0xC4)
expect(b[2]).to_equal(0x19)
expect(b[3]).to_equal(0x25)
```

</details>

#### pnext_s pd=5 pg=3

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = emit_pnext_s(5, 3)
expect(b[0]).to_equal(0x65)
expect(b[1]).to_equal(0xC4)
expect(b[2]).to_equal(0x19)
expect(b[3]).to_equal(0x25)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/sve2_pred_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SVE2 predicate emit golden bytes
- PTRUE
- PFALSE
- WHILELT
- WHILELE
- AND predicate
- ORR predicate
- EOR predicate
- NOT predicate
- BRKA
- PNEXT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
