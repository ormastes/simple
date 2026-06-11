# Rvv Widen Specification

> <details>

<!-- sdn-diagram:id=rvv_widen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvv_widen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvv_widen_spec -> std
rvv_widen_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvv_widen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Widen Specification

## Scenarios

### encode_rvv_widen — vwaddu.vv (widening unsigned add)

#### emit_vwaddu_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x30,vm=1,vs2=0,vs1=0,funct3=2,vd=0 → word=0xC2002057
val got = emit_vwaddu_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xC2)
```

</details>

#### emit_vwaddu_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x30,vm=1,vs2=2,vs1=3,funct3=2,vd=1 → word=0xC221A0D7
val got = emit_vwaddu_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xC2)
```

</details>

### encode_rvv_widen — vwsubu.vv (widening unsigned sub)

#### emit_vwsubu_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x32,vm=1,vs2=0,vs1=0,funct3=2,vd=0 → word=0xCA002057
val got = emit_vwsubu_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xCA)
```

</details>

#### emit_vwsubu_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x32,vm=1,vs2=2,vs1=3,funct3=2,vd=1 → word=0xCA21A0D7
val got = emit_vwsubu_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xCA)
```

</details>

### encode_rvv_widen — vwadd.vv (widening signed add)

#### emit_vwadd_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x31,vm=1,vs2=0,vs1=0,funct3=2,vd=0 → word=0xC6002057
val got = emit_vwadd_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xC6)
```

</details>

#### emit_vwadd_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x31,vm=1,vs2=2,vs1=3,funct3=2,vd=1 → word=0xC621A0D7
val got = emit_vwadd_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xC6)
```

</details>

### encode_rvv_widen — vwsub.vv (widening signed sub)

#### emit_vwsub_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x33,vm=1,vs2=0,vs1=0,funct3=2,vd=0 → word=0xCE002057
val got = emit_vwsub_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xCE)
```

</details>

#### emit_vwsub_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x33,vm=1,vs2=2,vs1=3,funct3=2,vd=1 → word=0xCE21A0D7
val got = emit_vwsub_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xCE)
```

</details>

### encode_rvv_widen — vnsrl.wv (narrowing shift right logical, OPIVV funct3=0)

#### emit_vnsrl_wv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2C,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0xB2000057
val got = emit_vnsrl_wv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xB2)
```

</details>

#### emit_vnsrl_wv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2C,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0xB22180D7
# NOTE: byte[1]=0x80 (not 0xA0) because funct3=0 not 2
val got = emit_vnsrl_wv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xB2)
```

</details>

### encode_rvv_widen — vnsra.wv (narrowing shift right arithmetic, OPIVV funct3=0)

#### emit_vnsra_wv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2D,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0xB6000057
val got = emit_vnsra_wv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xB6)
```

</details>

#### emit_vnsra_wv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2D,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0xB62180D7
# NOTE: byte[1]=0x80 (not 0xA0) because funct3=0 not 2
val got = emit_vnsra_wv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xB6)
```

</details>

### encode_rvv_widen — vwmul.vv (widening signed multiply)

#### emit_vwmul_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x3B,vm=1,vs2=0,vs1=0,funct3=2,vd=0 → word=0xEE002057
val got = emit_vwmul_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xEE)
```

</details>

#### emit_vwmul_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x3B,vm=1,vs2=2,vs1=3,funct3=2,vd=1 → word=0xEE21A0D7
val got = emit_vwmul_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xEE)
```

</details>

### encode_rvv_widen — vwmulu.vv (widening unsigned multiply)

#### emit_vwmulu_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x38,vm=1,vs2=0,vs1=0,funct3=2,vd=0 → word=0xE2002057
val got = emit_vwmulu_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xE2)
```

</details>

#### emit_vwmulu_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x38,vm=1,vs2=2,vs1=3,funct3=2,vd=1 → word=0xE221A0D7
val got = emit_vwmulu_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xE2)
```

</details>

### encode_rvv_widen — funct3 discriminator sanity

#### vwaddu_vv and vnsrl_wv differ in byte[1] (funct3 field)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# OPMVV funct3=2 vs OPIVV funct3=0 — byte[1] bit[1:0] differs
# vwaddu: funct3=2 → byte[1]=0xA0 (with vs1=3); vnsrl: funct3=0 → byte[1]=0x80
val widen = emit_vwaddu_vv(1, 2, 3)
val narrow = emit_vnsrl_wv(1, 2, 3)
expect(widen[0]) to_equal(narrow[0])
expect(widen[2]) to_equal(narrow[2])
expect(widen[1]) to_equal(0xA0)
expect(narrow[1]) to_equal(0x80)
```

</details>

#### vnsrl_wv and vnsra_wv share byte[1] but differ in byte[3] (funct6)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2C vs 0x2D — differ by 1 in bits[31:26] → byte[3]
val srl = emit_vnsrl_wv(1, 2, 3)
val sra = emit_vnsra_wv(1, 2, 3)
expect(srl[0]) to_equal(sra[0])
expect(srl[1]) to_equal(sra[1])
expect(srl[3]) to_equal(0xB2)
expect(sra[3]) to_equal(0xB6)
```

</details>

#### all 8 emit functions return 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vwaddu_vv(0, 0, 0).length) to_equal(4)
expect(emit_vwsubu_vv(0, 0, 0).length) to_equal(4)
expect(emit_vwadd_vv(0, 0, 0).length) to_equal(4)
expect(emit_vwsub_vv(0, 0, 0).length) to_equal(4)
expect(emit_vnsrl_wv(0, 0, 0).length) to_equal(4)
expect(emit_vnsra_wv(0, 0, 0).length) to_equal(4)
expect(emit_vwmul_vv(0, 0, 0).length) to_equal(4)
expect(emit_vwmulu_vv(0, 0, 0).length) to_equal(4)
```

</details>

#### byte[0] is always 0x57 (OP-V opcode) for all ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vwaddu_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vwsubu_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vwadd_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vwsub_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vnsrl_wv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vnsra_wv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vwmul_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vwmulu_vv(0, 0, 0)[0]) to_equal(0x57)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/rvv_widen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- encode_rvv_widen — vwaddu.vv (widening unsigned add)
- encode_rvv_widen — vwsubu.vv (widening unsigned sub)
- encode_rvv_widen — vwadd.vv (widening signed add)
- encode_rvv_widen — vwsub.vv (widening signed sub)
- encode_rvv_widen — vnsrl.wv (narrowing shift right logical, OPIVV funct3=0)
- encode_rvv_widen — vnsra.wv (narrowing shift right arithmetic, OPIVV funct3=0)
- encode_rvv_widen — vwmul.vv (widening signed multiply)
- encode_rvv_widen — vwmulu.vv (widening unsigned multiply)
- encode_rvv_widen — funct3 discriminator sanity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
