# Rvv Fixedpt Specification

> <details>

<!-- sdn-diagram:id=rvv_fixedpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvv_fixedpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvv_fixedpt_spec -> std
rvv_fixedpt_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvv_fixedpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Fixedpt Specification

## Scenarios

### RVV fixed-point vssrl.vv

#### emit_vssrl_vv(1,2,3) golden 0xAA2180D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2A, OPIVV funct3=0, vm=1: word=0xAA2180D7 LE d78021aa
val bytes = emit_vssrl_vv(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d78021aa")
```

</details>

#### emit_vssrl_vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vssrl_vv(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

#### emit_vssrl_vv opcode byte is 0xD7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vssrl_vv(1, 2, 3)
expect(bytes[0]).to_equal(215)
```

</details>

### RVV fixed-point vssra.vv

#### emit_vssra_vv(1,2,3) golden 0xAE2180D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2B, OPIVV funct3=0, vm=1: word=0xAE2180D7 LE d78021ae
val bytes = emit_vssra_vv(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d78021ae")
```

</details>

#### emit_vssra_vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vssra_vv(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

### RVV fixed-point vnclipu.wv

#### emit_vnclipu_wv(1,2,3) golden 0xBA2180D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2E, OPIVV funct3=0, vm=1: word=0xBA2180D7 LE d78021ba
val bytes = emit_vnclipu_wv(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d78021ba")
```

</details>

#### emit_vnclipu_wv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vnclipu_wv(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

### RVV fixed-point vnclip.wv

#### emit_vnclip_wv(1,2,3) golden 0xBE2180D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2F, OPIVV funct3=0, vm=1: word=0xBE2180D7 LE d78021be
val bytes = emit_vnclip_wv(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d78021be")
```

</details>

#### emit_vnclip_wv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vnclip_wv(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

### RVV fixed-point vssrl.vx

#### emit_vssrl_vx(1,2,3) golden 0xAA21C0D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2A, OPIVX funct3=4, vm=1: word=0xAA21C0D7 LE d7c021aa
val bytes = emit_vssrl_vx(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d7c021aa")
```

</details>

#### emit_vssrl_vx output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vssrl_vx(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

#### emit_vssrl_vx funct3 differs from emit_vssrl_vv (byte index 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vv = emit_vssrl_vv(1, 2, 3)
val vx = emit_vssrl_vx(1, 2, 3)
expect(vv[1] == vx[1]).to_equal(false)
```

</details>

### RVV fixed-point vssra.vx

#### emit_vssra_vx(1,2,3) golden 0xAE21C0D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2B, OPIVX funct3=4, vm=1: word=0xAE21C0D7 LE d7c021ae
val bytes = emit_vssra_vx(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d7c021ae")
```

</details>

#### emit_vssra_vx output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vssra_vx(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

### RVV fixed-point vsaddu.vv

#### emit_vsaddu_vv(1,2,3) golden 0x822180D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x20, OPIVV funct3=0, vm=1: word=0x822180D7 LE d7802182
val bytes = emit_vsaddu_vv(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d7802182")
```

</details>

#### emit_vsaddu_vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vsaddu_vv(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

### RVV fixed-point vsadd.vv

#### emit_vsadd_vv(1,2,3) golden 0x862180D7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x21, OPIVV funct3=0, vm=1: word=0x862180D7 LE d7802186
val bytes = emit_vsadd_vv(1, 2, 3)
expect(_list_hex(bytes)).to_equal("d7802186")
```

</details>

#### emit_vsadd_vv output length is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = emit_vsadd_vv(1, 2, 3)
expect(bytes.len()).to_equal(4)
```

</details>

#### emit_vsadd_vv funct6 differs from emit_vsaddu_vv (byte index 3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val u = emit_vsaddu_vv(1, 2, 3)
val s = emit_vsadd_vv(1, 2, 3)
expect(u[3] == s[3]).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/rvv_fixedpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RVV fixed-point vssrl.vv
- RVV fixed-point vssra.vv
- RVV fixed-point vnclipu.wv
- RVV fixed-point vnclip.wv
- RVV fixed-point vssrl.vx
- RVV fixed-point vssra.vx
- RVV fixed-point vsaddu.vv
- RVV fixed-point vsadd.vv

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
