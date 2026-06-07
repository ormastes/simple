# Rvv Int Emit Specification

> <details>

<!-- sdn-diagram:id=rvv_int_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvv_int_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvv_int_emit_spec -> std
rvv_int_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvv_int_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Int Emit Specification

## Scenarios

### encode_rvv_int — vadd.vv (vector add, §11.1)

#### emit_vadd_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x00,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0x02000057
val got = emit_vadd_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x02)
```

</details>

#### emit_vadd_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x00,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0x022180D7
val got = emit_vadd_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x02)
```

</details>

### encode_rvv_int — vsub.vv (vector subtract, §11.1)

#### emit_vsub_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x02,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0x0A000057
val got = emit_vsub_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x0A)
```

</details>

#### emit_vsub_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x02,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0x0A2180D7
val got = emit_vsub_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x0A)
```

</details>

### encode_rvv_int — vand.vv (vector AND, §11.4)

#### emit_vand_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x09,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0x26000057
val got = emit_vand_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x26)
```

</details>

#### emit_vand_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x09,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0x262180D7
val got = emit_vand_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x26)
```

</details>

### encode_rvv_int — vor.vv (vector OR, §11.4)

#### emit_vor_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x0A,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0x2A000057
val got = emit_vor_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x2A)
```

</details>

#### emit_vor_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x0A,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0x2A2180D7
val got = emit_vor_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x2A)
```

</details>

### encode_rvv_int — vxor.vv (vector XOR, §11.4)

#### emit_vxor_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x0B,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0x2E000057
val got = emit_vxor_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x2E)
```

</details>

#### emit_vxor_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x0B,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0x2E2180D7
val got = emit_vxor_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x2E)
```

</details>

### encode_rvv_int — vsll.vv (vector shift left logical, §11.6)

#### emit_vsll_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x25,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0x96000057
val got = emit_vsll_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x96)
```

</details>

#### emit_vsll_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x25,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0x962180D7
val got = emit_vsll_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x96)
```

</details>

### encode_rvv_int — vsrl.vv (vector shift right logical, §11.6)

#### emit_vsrl_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x28,vm=1,vs2=0,vs1=0,funct3=0,vd=0 → word=0xA2000057
val got = emit_vsrl_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x00)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xA2)
```

</details>

#### emit_vsrl_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x28,vm=1,vs2=2,vs1=3,funct3=0,vd=1 → word=0xA22180D7
val got = emit_vsrl_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x80)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xA2)
```

</details>

### encode_rvv_int — vmul.vv (vector multiply low, §11.10)

#### emit_vmul_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x25,vm=1,vs2=0,vs1=0,funct3=2,vd=0 → word=0x96002057
val got = emit_vmul_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x96)
```

</details>

#### emit_vmul_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x25,vm=1,vs2=2,vs1=3,funct3=2,vd=1 → word=0x962120D7
val got = emit_vmul_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x96)
```

</details>

### encode_rvv_int — cross-op discriminator sanity

#### all 8 emit functions return 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vadd_vv(0, 0, 0).length) to_equal(4)
expect(emit_vsub_vv(0, 0, 0).length) to_equal(4)
expect(emit_vand_vv(0, 0, 0).length) to_equal(4)
expect(emit_vor_vv(0, 0, 0).length) to_equal(4)
expect(emit_vxor_vv(0, 0, 0).length) to_equal(4)
expect(emit_vsll_vv(0, 0, 0).length) to_equal(4)
expect(emit_vsrl_vv(0, 0, 0).length) to_equal(4)
expect(emit_vmul_vv(0, 0, 0).length) to_equal(4)
```

</details>

#### byte[0] is always 0x57 (OP-V opcode) for all ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vadd_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vsub_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vand_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vor_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vxor_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vsll_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vsrl_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmul_vv(0, 0, 0)[0]) to_equal(0x57)
```

</details>

#### vsll.vv and vmul.vv share funct6=0x25 but differ in byte[1] (funct3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vsll: funct3=0 → byte[1]=0x00; vmul: funct3=2 → byte[1]=0x20
val sll = emit_vsll_vv(0, 0, 0)
val mul = emit_vmul_vv(0, 0, 0)
expect(sll[0]) to_equal(mul[0])
expect(sll[2]) to_equal(mul[2])
expect(sll[3]) to_equal(mul[3])
expect(sll[1]) to_equal(0x00)
expect(mul[1]) to_equal(0x20)
```

</details>

#### vadd.vv and vsub.vv differ only in byte[3] (funct6)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vadd funct6=0x00 byte[3]=0x02; vsub funct6=0x02 byte[3]=0x0A
val add_op = emit_vadd_vv(1, 2, 3)
val sub_op = emit_vsub_vv(1, 2, 3)
expect(add_op[0]) to_equal(sub_op[0])
expect(add_op[1]) to_equal(sub_op[1])
expect(add_op[2]) to_equal(sub_op[2])
expect(add_op[3]) to_equal(0x02)
expect(sub_op[3]) to_equal(0x0A)
```

</details>

#### vsrl.vv (funct6=0x28) byte[3] > vsll.vv (funct6=0x25) byte[3]

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sll = emit_vsll_vv(0, 0, 0)
val srl = emit_vsrl_vv(0, 0, 0)
expect(sll[3]) to_equal(0x96)
expect(srl[3]) to_equal(0xA2)
```

</details>

#### emit_vadd_vv vd=4 vs2=5 vs1=6 — higher register numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x00,vm=1,vs2=5,vs1=6,funct3=0,vd=4 → word=0x02530257
val got = emit_vadd_vv(4, 5, 6)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x02)
expect(got[2]) to_equal(0x53)
expect(got[3]) to_equal(0x02)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/rvv_int_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- encode_rvv_int — vadd.vv (vector add, §11.1)
- encode_rvv_int — vsub.vv (vector subtract, §11.1)
- encode_rvv_int — vand.vv (vector AND, §11.4)
- encode_rvv_int — vor.vv (vector OR, §11.4)
- encode_rvv_int — vxor.vv (vector XOR, §11.4)
- encode_rvv_int — vsll.vv (vector shift left logical, §11.6)
- encode_rvv_int — vsrl.vv (vector shift right logical, §11.6)
- encode_rvv_int — vmul.vv (vector multiply low, §11.10)
- encode_rvv_int — cross-op discriminator sanity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
