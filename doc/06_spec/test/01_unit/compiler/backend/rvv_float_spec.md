# Rvv Float Specification

> <details>

<!-- sdn-diagram:id=rvv_float_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvv_float_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvv_float_spec -> std
rvv_float_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvv_float_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Float Specification

## Scenarios

### encode_rvv_float — vfadd.vv (FP add, OPFVV funct3=1)

#### emit_vfadd_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x00,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0x02001057
val got = emit_vfadd_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x02)
```

</details>

#### emit_vfadd_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x00,vm=1,vs2=2,vs1=3,funct3=1,vd=1 → word=0x022190D7
val got = emit_vfadd_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x90)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x02)
```

</details>

### encode_rvv_float — vfsub.vv (FP subtract, OPFVV funct3=1)

#### emit_vfsub_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x02,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0x0A001057
val got = emit_vfsub_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x0A)
```

</details>

#### emit_vfsub_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x02,vm=1,vs2=2,vs1=3,funct3=1,vd=1 → word=0x0A2190D7
val got = emit_vfsub_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x90)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x0A)
```

</details>

### encode_rvv_float — vfmin.vv (FP minimum, OPFVV funct3=1)

#### emit_vfmin_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x04,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0x12001057
val got = emit_vfmin_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x12)
```

</details>

#### emit_vfmin_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x04,vm=1,vs2=2,vs1=3,funct3=1,vd=1 → word=0x122190D7
val got = emit_vfmin_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x90)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x12)
```

</details>

### encode_rvv_float — vfmax.vv (FP maximum, OPFVV funct3=1)

#### emit_vfmax_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x06,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0x1A001057
val got = emit_vfmax_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x1A)
```

</details>

#### emit_vfmax_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x06,vm=1,vs2=2,vs1=3,funct3=1,vd=1 → word=0x1A2190D7
val got = emit_vfmax_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x90)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x1A)
```

</details>

### encode_rvv_float — vfmul.vv (FP multiply, OPFVV funct3=1)

#### emit_vfmul_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x24,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0x92001057
val got = emit_vfmul_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x92)
```

</details>

#### emit_vfmul_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x24,vm=1,vs2=2,vs1=3,funct3=1,vd=1 → word=0x922190D7
val got = emit_vfmul_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x90)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x92)
```

</details>

### encode_rvv_float — vfdiv.vv (FP divide, OPFVV funct3=1)

#### emit_vfdiv_vv vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x20,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0x82001057
val got = emit_vfdiv_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x82)
```

</details>

#### emit_vfdiv_vv vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x20,vm=1,vs2=2,vs1=3,funct3=1,vd=1 → word=0x822190D7
val got = emit_vfdiv_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x90)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x82)
```

</details>

### encode_rvv_float — vfmadd.vv (FP fused multiply-add, OPFVV funct3=1)

#### emit_vfmadd_vv vd=0 vs1=0 vs2=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x28,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0xA2001057
val got = emit_vfmadd_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xA2)
```

</details>

#### emit_vfmadd_vv vd=1 vs1=2 vs2=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# API: emit_vfmadd_vv(vd=1, vs1=2, vs2=3)
# Encoding: funct6=0x28,vm=1,vs2_field=3,vs1_field=2,funct3=1,vd=1
# word=0xA23110D7 LE [0xD7,0x10,0x31,0xA2]
val got = emit_vfmadd_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x31)
expect(got[3]) to_equal(0xA2)
```

</details>

### encode_rvv_float — vfmsub.vv (FP fused multiply-sub, OPFVV funct3=1)

#### emit_vfmsub_vv vd=0 vs1=0 vs2=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2A,vm=1,vs2=0,vs1=0,funct3=1,vd=0 → word=0xAA001057
val got = emit_vfmsub_vv(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0xAA)
```

</details>

#### emit_vfmsub_vv vd=1 vs1=2 vs2=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# API: emit_vfmsub_vv(vd=1, vs1=2, vs2=3)
# Encoding: funct6=0x2A,vm=1,vs2_field=3,vs1_field=2,funct3=1,vd=1
# word=0xAA3110D7 LE [0xD7,0x10,0x31,0xAA]
val got = emit_vfmsub_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x10)
expect(got[2]) to_equal(0x31)
expect(got[3]) to_equal(0xAA)
```

</details>

### encode_rvv_float — opcode and funct3 sanity

#### byte[0] is always 0x57 (OP-V opcode) for all ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vfadd_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vfsub_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vfmul_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vfdiv_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vfmadd_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vfmsub_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vfmin_vv(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vfmax_vv(0, 0, 0)[0]) to_equal(0x57)
```

</details>

#### all 8 emit functions return 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vfadd_vv(0, 0, 0).length) to_equal(4)
expect(emit_vfsub_vv(0, 0, 0).length) to_equal(4)
expect(emit_vfmul_vv(0, 0, 0).length) to_equal(4)
expect(emit_vfdiv_vv(0, 0, 0).length) to_equal(4)
expect(emit_vfmadd_vv(0, 0, 0).length) to_equal(4)
expect(emit_vfmsub_vv(0, 0, 0).length) to_equal(4)
expect(emit_vfmin_vv(0, 0, 0).length) to_equal(4)
expect(emit_vfmax_vv(0, 0, 0).length) to_equal(4)
```

</details>

#### vfadd and vfsub differ only in byte[3] (funct6 field)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x00 vs 0x02 — differ in byte[3]
val add = emit_vfadd_vv(1, 2, 3)
val sub = emit_vfsub_vv(1, 2, 3)
expect(add[0]) to_equal(sub[0])
expect(add[1]) to_equal(sub[1])
expect(add[2]) to_equal(sub[2])
expect(add[3]) to_equal(0x02)
expect(sub[3]) to_equal(0x0A)
```

</details>

#### vfmin and vfmax differ only in byte[3] (funct6 field)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x04 vs 0x06 — differ in byte[3]
val fmin = emit_vfmin_vv(1, 2, 3)
val fmax = emit_vfmax_vv(1, 2, 3)
expect(fmin[0]) to_equal(fmax[0])
expect(fmin[1]) to_equal(fmax[1])
expect(fmin[2]) to_equal(fmax[2])
expect(fmin[3]) to_equal(0x12)
expect(fmax[3]) to_equal(0x1A)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/rvv_float_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- encode_rvv_float — vfadd.vv (FP add, OPFVV funct3=1)
- encode_rvv_float — vfsub.vv (FP subtract, OPFVV funct3=1)
- encode_rvv_float — vfmin.vv (FP minimum, OPFVV funct3=1)
- encode_rvv_float — vfmax.vv (FP maximum, OPFVV funct3=1)
- encode_rvv_float — vfmul.vv (FP multiply, OPFVV funct3=1)
- encode_rvv_float — vfdiv.vv (FP divide, OPFVV funct3=1)
- encode_rvv_float — vfmadd.vv (FP fused multiply-add, OPFVV funct3=1)
- encode_rvv_float — vfmsub.vv (FP fused multiply-sub, OPFVV funct3=1)
- encode_rvv_float — opcode and funct3 sanity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
