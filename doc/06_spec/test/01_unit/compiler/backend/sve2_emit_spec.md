# Sve2 Emit Specification

> <details>

<!-- sdn-diagram:id=sve2_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sve2_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sve2_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sve2_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sve2 Emit Specification

## Scenarios

### SVE2 emit_sve2_add_s Z0.S golden

#### ADD Z0.S Z0.S Z0.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_add_s(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ADD Z0.S Z0.S Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[7:0]: Zd=0, Zn low bits=0
val result = emit_sve2_add_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

#### ADD Z0.S Z0.S Z0.S byte1 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: sub-opcode zeros
val result = emit_sve2_add_s(0, 0, 0)
expect(result[1]).to_equal(0)
```

</details>

#### ADD Z0.S Z0.S Z0.S byte2 is 0xA0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]: 0xA0 = 10100000 → bits[23:22]=10(S) bit[21]=1 Zm=0
val result = emit_sve2_add_s(0, 0, 0)
expect(result[2]).to_equal(160)
```

</details>

#### ADD Z0.S Z0.S Z0.S byte3 is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]: SVE integer arithmetic group
val result = emit_sve2_add_s(0, 0, 0)
expect(result[3]).to_equal(4)
```

</details>

### SVE2 emit_sve2_add_s Z1 Z2 Z3 register fields

#### ADD Z1.S Z2.S Z3.S byte0 encodes Zd and Zn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=1 bits[4:0]=1; Zn=2 bits[9:5]=2 → byte0 = 1 + (2*32) = 0x41
val result = emit_sve2_add_s(1, 2, 3)
expect(result[0]).to_equal(65)
```

</details>

#### ADD Z1.S Z2.S Z3.S byte1 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_add_s(1, 2, 3)
expect(result[1]).to_equal(0)
```

</details>

#### ADD Z1.S Z2.S Z3.S byte2 encodes Zm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=3 → bits[20:16]=3 → byte2 = 0xA0 + 3 = 0xA3
val result = emit_sve2_add_s(1, 2, 3)
expect(result[2]).to_equal(163)
```

</details>

#### ADD Z1.S Z2.S Z3.S byte3 is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_add_s(1, 2, 3)
expect(result[3]).to_equal(4)
```

</details>

### SVE2 emit_sve2_add_s Z31 boundary

#### ADD Z31.S Z31.S Z31.S byte0 is 0xFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zd=31=0x1F; Zn=31 in bits[9:5]=31*32=992; byte0=(31+992)%256=1023%256=0xFF
val result = emit_sve2_add_s(31, 31, 31)
expect(result[0]).to_equal(255)
```

</details>

#### ADD Z31.S Z31.S Z31.S byte1 is 0x03

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]: upper bits of Zn=31 overflow into byte1: 1023/256=3 remainder 255
val result = emit_sve2_add_s(31, 31, 31)
expect(result[1]).to_equal(3)
```

</details>

#### ADD Z31.S Z31.S Z31.S byte2 is 0xBF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=31 → bits[20:16]=31 → byte2 = 0xA0 + 31 = 0xBF
val result = emit_sve2_add_s(31, 31, 31)
expect(result[2]).to_equal(191)
```

</details>

#### ADD Z31.S Z31.S Z31.S byte3 is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_add_s(31, 31, 31)
expect(result[3]).to_equal(4)
```

</details>

### SVE2 ADD lane-size variants

#### ADD Z0.B byte2 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x20 → bits[23:22]=00(B) bit[21]=1
val result = emit_sve2_add_b(0, 0, 0)
expect(result[2]).to_equal(32)
```

</details>

#### ADD Z0.H byte2 is 0x60

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x60 → bits[23:22]=01(H) bit[21]=1
val result = emit_sve2_add_h(0, 0, 0)
expect(result[2]).to_equal(96)
```

</details>

#### ADD Z0.D byte2 is 0xE0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0xE0 → bits[23:22]=11(D) bit[21]=1
val result = emit_sve2_add_d(0, 0, 0)
expect(result[2]).to_equal(224)
```

</details>

#### ADD Z0.B emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_add_b(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ADD Z0.H emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_add_h(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

#### ADD Z0.D emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_add_d(0, 0, 0)
expect(result.len()).to_equal(4)
```

</details>

### SVE2 emit_sve2_mul_s golden

#### MUL Z0.S P0/M Z0.S Z1.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_mul_s(0, 0, 1)
expect(result.len()).to_equal(4)
```

</details>

#### MUL Z0.S P0/M Z0.S Z1.S byte0 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=1 in bits[9:5]=32; Zdn=0 bits[4:0]=0 → byte0=32=0x20
val result = emit_sve2_mul_s(0, 0, 1)
expect(result[0]).to_equal(32)
```

</details>

#### MUL Z0.S P0/M Z0.S Z1.S byte1 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_mul_s(0, 0, 1)
expect(result[1]).to_equal(0)
```

</details>

#### MUL Z0.S P0/M Z0.S Z1.S byte2 is 0x90

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x90 encodes predicated MUL S-element opcode with Pg=0
val result = emit_sve2_mul_s(0, 0, 1)
expect(result[2]).to_equal(144)
```

</details>

#### MUL Z0.S P0/M Z0.S Z1.S byte3 is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_mul_s(0, 0, 1)
expect(result[3]).to_equal(4)
```

</details>

#### MUL Z0.S P0/M Z0.S Z0.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=0, Zdn=0 → byte0=0
val result = emit_sve2_mul_s(0, 0, 0)
expect(result[0]).to_equal(0)
```

</details>

### SVE2 emit_sve2_fadd_s golden

#### FADD Z0.S P0/M Z0.S Z1.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_fadd_s(0, 0, 1)
expect(result.len()).to_equal(4)
```

</details>

#### FADD Z0.S P0/M Z0.S Z1.S byte0 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=1 in bits[9:5]=32; zdn=0 → byte0=32=0x20
val result = emit_sve2_fadd_s(0, 0, 1)
expect(result[0]).to_equal(32)
```

</details>

#### FADD Z0.S P0/M Z0.S Z1.S byte1 is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x80: merging-predication bit + Pg=0
val result = emit_sve2_fadd_s(0, 0, 1)
expect(result[1]).to_equal(128)
```

</details>

#### FADD Z0.S P0/M Z0.S Z1.S byte2 is 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]=0x80: S-size encoding for FP predicated add
val result = emit_sve2_fadd_s(0, 0, 1)
expect(result[2]).to_equal(128)
```

</details>

#### FADD Z0.S P0/M Z0.S Z1.S byte3 is 0x65

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[31:24]=0x65: SVE FP arithmetic group
val result = emit_sve2_fadd_s(0, 0, 1)
expect(result[3]).to_equal(101)
```

</details>

### SVE2 FADD size variants

#### FADD Z0.H P0/M Z0.H Z1.H byte2 is 0x40

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:22]=01(H) → byte2=0x40
val result = emit_sve2_fadd_h(0, 0, 1)
expect(result[2]).to_equal(64)
```

</details>

#### FADD Z0.D P0/M Z0.D Z1.D byte2 is 0xC0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:22]=11(D) → byte2=0xC0
val result = emit_sve2_fadd_d(0, 0, 1)
expect(result[2]).to_equal(192)
```

</details>

#### FADD Z0.H emits byte3 0x65

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_fadd_h(0, 0, 1)
expect(result[3]).to_equal(101)
```

</details>

#### FADD Z0.D emits byte3 0x65

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_fadd_d(0, 0, 1)
expect(result[3]).to_equal(101)
```

</details>

### SVE2 emit_sve2_fmla_s golden

#### FMLA Z0.S P0/M Z1.S Z2.S emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_fmla_s(0, 0, 1, 2)
expect(result.len()).to_equal(4)
```

</details>

#### FMLA Z0.S P0/M Z1.S Z2.S byte0 is 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zda=0; Zn=1 bits[9:5]=32 → byte0=32=0x20
val result = emit_sve2_fmla_s(0, 0, 1, 2)
expect(result[0]).to_equal(32)
```

</details>

#### FMLA Z0.S P0/M Z1.S Z2.S byte1 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pg=0 in bits[12:10]; no overflow into byte1
val result = emit_sve2_fmla_s(0, 0, 1, 2)
expect(result[1]).to_equal(0)
```

</details>

#### FMLA Z0.S P0/M Z1.S Z2.S byte2 is 0xA2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[23:16]: FMLA S base=0xA0; Zm=2 in bits[20:16]=+2 → 0xA2
val result = emit_sve2_fmla_s(0, 0, 1, 2)
expect(result[2]).to_equal(162)
```

</details>

#### FMLA Z0.S P0/M Z1.S Z2.S byte3 is 0x65

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_fmla_s(0, 0, 1, 2)
expect(result[3]).to_equal(101)
```

</details>

#### FMLA Z0.S P0/M Z0.S Z1.S byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zda=0, Zn=0 → byte0=0; Zm=1 → byte2=0xA1
val result = emit_sve2_fmla_s(0, 0, 0, 1)
expect(result[0]).to_equal(0)
```

</details>

#### FMLA Z0.S P0/M Z0.S Z1.S byte2 is 0xA1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zm=1 bits[20:16]=1 → byte2=0xA0+1=0xA1
val result = emit_sve2_fmla_s(0, 0, 0, 1)
expect(result[2]).to_equal(161)
```

</details>

### SVE2 emit_sve2_whilelo_s golden

#### WHILELO P0.S X0 X1 emits 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = emit_sve2_whilelo_s(0, 0, 1)
expect(result.len()).to_equal(4)
```

</details>

#### WHILELO P0.S X0 X1 byte0 is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pd=0, Xn=0 → byte0=0
val result = emit_sve2_whilelo_s(0, 0, 1)
expect(result[0]).to_equal(0)
```

</details>

#### WHILELO P0.S X0 X1 byte1 is 0x1C

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# bits[15:8]=0x1C: opcode sub-field for WHILELO
val result = emit_sve2_whilelo_s(0, 0, 1)
expect(result[1]).to_equal(28)
```

</details>

#### WHILELO P0.S X0 X1 byte2 is 0xA1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Xm=1 in bits[20:16]=1; base bits[23:16]=0xA0 → byte2=0xA1
val result = emit_sve2_whilelo_s(0, 0, 1)
expect(result[2]).to_equal(161)
```

</details>

#### WHILELO P0.S X0 X1 byte3 is 0x25

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SVE predicate-forming group opcode
val result = emit_sve2_whilelo_s(0, 0, 1)
expect(result[3]).to_equal(37)
```

</details>

#### WHILELO P1.S X0 X1 byte0 is 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pd=1 → bits[3:0]=1 → byte0=1
val result = emit_sve2_whilelo_s(1, 0, 1)
expect(result[0]).to_equal(1)
```

</details>

#### WHILELO P0.S X0 X2 byte2 is 0xA2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Xm=2 in bits[20:16]=2 → byte2=0xA0+2=0xA2
val result = emit_sve2_whilelo_s(0, 0, 2)
expect(result[2]).to_equal(162)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/sve2_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SVE2 emit_sve2_add_s Z0.S golden
- SVE2 emit_sve2_add_s Z1 Z2 Z3 register fields
- SVE2 emit_sve2_add_s Z31 boundary
- SVE2 ADD lane-size variants
- SVE2 emit_sve2_mul_s golden
- SVE2 emit_sve2_fadd_s golden
- SVE2 FADD size variants
- SVE2 emit_sve2_fmla_s golden
- SVE2 emit_sve2_whilelo_s golden

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
