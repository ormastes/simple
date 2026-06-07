# Rvv Mask Emit Specification

> <details>

<!-- sdn-diagram:id=rvv_mask_emit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvv_mask_emit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvv_mask_emit_spec -> std
rvv_mask_emit_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvv_mask_emit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Mask Emit Specification

## Scenarios

### encode_rvv_mask — vmand.mm (mask AND)

#### emit_vmand_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x19,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x64002057
val got = emit_vmand_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x64)
```

</details>

#### emit_vmand_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x19,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x6421A0D7
val got = emit_vmand_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x64)
```

</details>

### encode_rvv_mask — vmnand.mm (mask NAND)

#### emit_vmnand_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1D,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x74002057
val got = emit_vmnand_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x74)
```

</details>

#### emit_vmnand_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1D,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x7421A0D7
val got = emit_vmnand_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x74)
```

</details>

### encode_rvv_mask — vmandn.mm (mask AND-NOT)

#### emit_vmand_not_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x18,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x60002057
val got = emit_vmand_not_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x60)
```

</details>

#### emit_vmand_not_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x18,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x6021A0D7
val got = emit_vmand_not_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x60)
```

</details>

### encode_rvv_mask — vmor.mm (mask OR)

#### emit_vmor_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1A,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x68002057
val got = emit_vmor_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x68)
```

</details>

#### emit_vmor_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1A,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x6821A0D7
val got = emit_vmor_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x68)
```

</details>

### encode_rvv_mask — vmnor.mm (mask NOR)

#### emit_vmnor_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1E,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x78002057
val got = emit_vmnor_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x78)
```

</details>

#### emit_vmnor_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1E,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x7821A0D7
val got = emit_vmnor_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x78)
```

</details>

### encode_rvv_mask — vmorn.mm (mask OR-NOT)

#### emit_vmor_not_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1C,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x70002057
val got = emit_vmor_not_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x70)
```

</details>

#### emit_vmor_not_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1C,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x7021A0D7
val got = emit_vmor_not_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x70)
```

</details>

### encode_rvv_mask — vmxor.mm (mask XOR)

#### emit_vmxor_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1B,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x6C002057
val got = emit_vmxor_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x6C)
```

</details>

#### emit_vmxor_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1B,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x6C21A0D7
val got = emit_vmxor_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x6C)
```

</details>

### encode_rvv_mask — vmxnor.mm (mask XNOR)

#### emit_vmxnor_mm vd=0 vs2=0 vs1=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1F,vm=0,vs2=0,vs1=0,funct3=2,vd=0 → word=0x7C002057
val got = emit_vmxnor_mm(0, 0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x00)
expect(got[3]) to_equal(0x7C)
```

</details>

#### emit_vmxnor_mm vd=1 vs2=2 vs1=3 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x1F,vm=0,vs2=2,vs1=3,funct3=2,vd=1 → word=0x7C21A0D7
val got = emit_vmxnor_mm(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x7C)
```

</details>

### encode_rvv_mask — vcpop.m (count population of mask)

#### emit_vcpop_m rd=0 vs2=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x10,vm=1,vs2=0,vs1=16,funct3=2,rd=0 → word=0x42082057
val got = emit_vcpop_m(0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x08)
expect(got[3]) to_equal(0x42)
```

</details>

#### emit_vcpop_m rd=1 vs2=2 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x10,vm=1,vs2=2,vs1=16,funct3=2,rd=1 → word=0x422820D7
val got = emit_vcpop_m(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x28)
expect(got[3]) to_equal(0x42)
```

</details>

### encode_rvv_mask — vfirst.m (find first set mask bit)

#### emit_vfirst_m rd=0 vs2=0 — zero-register canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x10,vm=1,vs2=0,vs1=17,funct3=2,rd=0 → word=0x4208A057
val got = emit_vfirst_m(0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x08)
expect(got[3]) to_equal(0x42)
```

</details>

#### emit_vfirst_m rd=1 vs2=2 — non-zero registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x10,vm=1,vs2=2,vs1=17,funct3=2,rd=1 → word=0x4228A0D7
val got = emit_vfirst_m(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x28)
expect(got[3]) to_equal(0x42)
```

</details>

### encode_rvv_mask — cross-op discriminator sanity

#### all 10 emit functions return 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vmand_mm(0, 0, 0).length) to_equal(4)
expect(emit_vmnand_mm(0, 0, 0).length) to_equal(4)
expect(emit_vmand_not_mm(0, 0, 0).length) to_equal(4)
expect(emit_vmor_mm(0, 0, 0).length) to_equal(4)
expect(emit_vmnor_mm(0, 0, 0).length) to_equal(4)
expect(emit_vmor_not_mm(0, 0, 0).length) to_equal(4)
expect(emit_vmxor_mm(0, 0, 0).length) to_equal(4)
expect(emit_vmxnor_mm(0, 0, 0).length) to_equal(4)
expect(emit_vcpop_m(0, 0).length) to_equal(4)
expect(emit_vfirst_m(0, 0).length) to_equal(4)
```

</details>

#### byte[0] is always 0x57 (OP-V opcode) for all ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vmand_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmnand_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmand_not_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmor_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmnor_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmor_not_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmxor_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vmxnor_mm(0, 0, 0)[0]) to_equal(0x57)
expect(emit_vcpop_m(0, 0)[0]) to_equal(0x57)
expect(emit_vfirst_m(0, 0)[0]) to_equal(0x57)
```

</details>

#### vmand.mm and vmnand.mm differ only in byte[3] (funct6 bit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vmand funct6=0x19 byte[3]=0x64; vmnand funct6=0x1D byte[3]=0x74
val and_op = emit_vmand_mm(1, 2, 3)
val nand_op = emit_vmnand_mm(1, 2, 3)
expect(and_op[0]) to_equal(nand_op[0])
expect(and_op[1]) to_equal(nand_op[1])
expect(and_op[2]) to_equal(nand_op[2])
expect(and_op[3]) to_equal(0x64)
expect(nand_op[3]) to_equal(0x74)
```

</details>

#### vcpop.m and vfirst.m share funct6/vm but differ in byte[1] (vs1 sub-op)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vcpop vs1=16 → byte[1] bit has vs1[0]=0; vfirst vs1=17 → vs1[0]=1 sets bit
val pop_op = emit_vcpop_m(1, 2)
val first_op = emit_vfirst_m(1, 2)
expect(pop_op[0]) to_equal(first_op[0])
expect(pop_op[2]) to_equal(first_op[2])
expect(pop_op[3]) to_equal(first_op[3])
expect(pop_op[1]) to_equal(0x20)
expect(first_op[1]) to_equal(0xA0)
```

</details>

#### mask-mask ops (vm=0) have byte[3] < 0x80 for funct6 < 0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# vm=0 means bit[25]=0; funct6 in 0x18-0x1F maps to byte[3] in 0x60-0x7F
expect(emit_vmand_mm(0, 0, 0)[3]) to_equal(0x64)
expect(emit_vmor_mm(0, 0, 0)[3]) to_equal(0x68)
expect(emit_vmxor_mm(0, 0, 0)[3]) to_equal(0x6C)
expect(emit_vmxnor_mm(0, 0, 0)[3]) to_equal(0x7C)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/rvv_mask_emit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- encode_rvv_mask — vmand.mm (mask AND)
- encode_rvv_mask — vmnand.mm (mask NAND)
- encode_rvv_mask — vmandn.mm (mask AND-NOT)
- encode_rvv_mask — vmor.mm (mask OR)
- encode_rvv_mask — vmnor.mm (mask NOR)
- encode_rvv_mask — vmorn.mm (mask OR-NOT)
- encode_rvv_mask — vmxor.mm (mask XOR)
- encode_rvv_mask — vmxnor.mm (mask XNOR)
- encode_rvv_mask — vcpop.m (count population of mask)
- encode_rvv_mask — vfirst.m (find first set mask bit)
- encode_rvv_mask — cross-op discriminator sanity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
