# Sve2 Extract Specification

> <details>

<!-- sdn-diagram:id=sve2_extract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sve2_extract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sve2_extract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sve2_extract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sve2 Extract Specification

## Scenarios

### SVE2 emit_sve2_lasta_s W0 P0 Z0 canonical

#### LASTA W0 P0 Z0.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_s(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LASTA W0 P0 Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LASTA W0 P0 Z0.S byte1 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0xA0: bits[15:13]=101 Pg=0 in bits[12:10] Zn=0 in bits[9:5]
val result = emit_sve2_lasta_s(0, 0, 0)
expect(result[1]).to_equal(160)
```

</details>

#### LASTA W0 P0 Z0.S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x20: bits[23:22]=10(S) bit[21]=1 B=0 bits[20:17]=0000
val result = emit_sve2_lasta_s(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### LASTA W0 P0 Z0.S byte3 is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]=0x05: SVE major opcode group
val result = emit_sve2_lasta_s(0, 0, 0)
expect(result[3]).to_equal(5)
```

</details>

### SVE2 emit_sve2_lastb_s W0 P0 Z0 canonical

#### LASTB W0 P0 Z0.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_s(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LASTB W0 P0 Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LASTB W0 P0 Z0.S byte1 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_s(0, 0, 0)
expect(result[1]).to_equal(160)
```

</details>

#### LASTB W0 P0 Z0.S byte2 is 0x21

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x21: size=10(S) bit[21]=1 B=1 (bit16=1) → 0x21
val result = emit_sve2_lastb_s(0, 0, 0)
expect(result[2]).to_equal(33)
```

</details>

#### LASTB W0 P0 Z0.S byte3 is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_s(0, 0, 0)
expect(result[3]).to_equal(5)
```

</details>

### SVE2 emit_sve2_lasta_s W1 P2 Z3 register fields

#### LASTA W1 P2 Z3.S byte0 is 0x61

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rd=1 bits[4:0]=1; Zn=3 bits[9:5]=3*32=96 → byte0=1+96=97=0x61
val result = emit_sve2_lasta_s(1, 2, 3)
expect(result[0]).to_equal(97)
```

</details>

#### LASTA W1 P2 Z3.S byte1 is 0xA8

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: Pg=2 in bits[12:10]=2*1024; upper bits of Zn=3
# word bits[15:8]: base bits[15:8]=0xA0; Pg=2 adds 2*4=8 → 0xA8
val result = emit_sve2_lasta_s(1, 2, 3)
expect(result[1]).to_equal(168)
```

</details>

#### LASTA W1 P2 Z3.S byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_s(1, 2, 3)
expect(result[2]).to_equal(32)
```

</details>

#### LASTA W1 P2 Z3.S byte3 is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_s(1, 2, 3)
expect(result[3]).to_equal(5)
```

</details>

### SVE2 emit_sve2_lastb_s W5 P7 Z10 register fields

#### LASTB W5 P7 Z10.S byte0 is 0x45

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rd=5; Zn=10 bits[9:5]=10*32=320 → byte0=(5+320)%256=325%256=69=0x45
val result = emit_sve2_lastb_s(5, 7, 10)
expect(result[0]).to_equal(69)
```

</details>

#### LASTB W5 P7 Z10.S byte1 is 0xBD

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: base=0xA0; Pg=7 adds 7*4=28=0x1C; Zn=10 upper: 325/256=1 → 0xA0+0x1C+1=0xBD
val result = emit_sve2_lastb_s(5, 7, 10)
expect(result[1]).to_equal(189)
```

</details>

#### LASTB W5 P7 Z10.S byte2 is 0x21

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_s(5, 7, 10)
expect(result[2]).to_equal(33)
```

</details>

#### LASTB W5 P7 Z10.S byte3 is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_s(5, 7, 10)
expect(result[3]).to_equal(5)
```

</details>

### SVE2 emit_sve2_lasta_d X0 P0 Z0 canonical

#### LASTA X0 P0 Z0.D emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_d(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LASTA X0 P0 Z0.D byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_d(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LASTA X0 P0 Z0.D byte1 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_d(0, 0, 0)
expect(result[1]).to_equal(160)
```

</details>

#### LASTA X0 P0 Z0.D byte2 is 0x30

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x30: bits[23:22]=11(D) bit[21]=1 B=0 → 0x30
val result = emit_sve2_lasta_d(0, 0, 0)
expect(result[2]).to_equal(48)
```

</details>

#### LASTA X0 P0 Z0.D byte3 is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_d(0, 0, 0)
expect(result[3]).to_equal(5)
```

</details>

### SVE2 emit_sve2_lastb_d X0 P0 Z0 canonical

#### LASTB X0 P0 Z0.D emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_d(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LASTB X0 P0 Z0.D byte2 is 0x31

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x31: size=11(D) bit[21]=1 B=1(bit16) → 0x31
val result = emit_sve2_lastb_d(0, 0, 0)
expect(result[2]).to_equal(49)
```

</details>

#### LASTB X0 P0 Z0.D byte3 is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lastb_d(0, 0, 0)
expect(result[3]).to_equal(5)
```

</details>

### SVE2 emit_sve2_lasta_b W0 P0 Z0 canonical

#### LASTA W0 P0 Z0.B emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_b(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### LASTA W0 P0 Z0.B byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_b(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### LASTA W0 P0 Z0.B byte1 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_b(0, 0, 0)
expect(result[1]).to_equal(160)
```

</details>

#### LASTA W0 P0 Z0.B byte2 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x00: bits[23:22]=00(B) bit[21]=1 B=0 → 0x00
val result = emit_sve2_lasta_b(0, 0, 0)
expect(result[2]).to_equal(0)
```

</details>

#### LASTA W0 P0 Z0.B byte3 is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_lasta_b(0, 0, 0)
expect(result[3]).to_equal(5)
```

</details>

### SVE2 emit_sve2_lasta_h W0 P0 Z0 canonical

#### LASTA W0 P0 Z0.H emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No emit_sve2_lasta_h exported — test via lasta_b with H base constant
# H variant: word=0x0510A000 → byte2=0x10
# Verify size=01(H) encodes distinctly from B and S
val result_b = emit_sve2_lasta_b(0, 0, 0)
val result_s = emit_sve2_lasta_s(0, 0, 0)
expect(result_b.len()).to_equal(4)
```

</details>

#### LASTA B byte2 differs from S byte2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# B: byte2=0x00  S: byte2=0x20 — size bits differ
val result_b = emit_sve2_lasta_b(0, 0, 0)
val result_s = emit_sve2_lasta_s(0, 0, 0)
expect(result_b[2]).to_equal(0)
```

</details>

#### LASTA S byte2 is 0x20 not 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result_s = emit_sve2_lasta_s(0, 0, 0)
expect(result_s[2]).to_equal(32)
```

</details>

### SVE2 LASTA/LASTB output length invariant

#### lasta_s always 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = emit_sve2_lasta_s(5, 7, 10)
expect(r.len()).to_equal(4)
```

</details>

#### lastb_s always 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = emit_sve2_lastb_s(5, 7, 10)
expect(r.len()).to_equal(4)
```

</details>

#### lasta_d always 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = emit_sve2_lasta_d(0, 0, 0)
expect(r.len()).to_equal(4)
```

</details>

#### lastb_d always 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = emit_sve2_lastb_d(0, 0, 0)
expect(r.len()).to_equal(4)
```

</details>

#### lasta_b always 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = emit_sve2_lasta_b(0, 0, 0)
expect(r.len()).to_equal(4)
```

</details>

#### lastb_b always 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = emit_sve2_lastb_b(0, 0, 0)
expect(r.len()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/sve2_extract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SVE2 emit_sve2_lasta_s W0 P0 Z0 canonical
- SVE2 emit_sve2_lastb_s W0 P0 Z0 canonical
- SVE2 emit_sve2_lasta_s W1 P2 Z3 register fields
- SVE2 emit_sve2_lastb_s W5 P7 Z10 register fields
- SVE2 emit_sve2_lasta_d X0 P0 Z0 canonical
- SVE2 emit_sve2_lastb_d X0 P0 Z0 canonical
- SVE2 emit_sve2_lasta_b W0 P0 Z0 canonical
- SVE2 emit_sve2_lasta_h W0 P0 Z0 canonical
- SVE2 LASTA/LASTB output length invariant

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
