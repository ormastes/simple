# Rvv Misc Specification

> <details>

<!-- sdn-diagram:id=rvv_misc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvv_misc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvv_misc_spec -> std
rvv_misc_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvv_misc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Misc Specification

## Scenarios

### encode_rvv_misc — vcpop.m

#### emit_vcpop_m rd=0 vs2=0 — canonical zero-register encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=16,vm=1,vs2=0,rs1=16,funct3=2,rd=0 → word=0x42082057
val got = emit_vcpop_m(0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x08)
expect(got[3]) to_equal(0x42)
```

</details>

#### emit_vcpop_m rd=1 vs2=2 — non-zero GPR and vector source

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=16,vm=1,vs2=2,rs1=16,funct3=2,rd=1 → word=0x422820D7
val got = emit_vcpop_m(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x28)
expect(got[3]) to_equal(0x42)
```

</details>

### encode_rvv_misc — vfirst.m

#### emit_vfirst_m rd=0 vs2=0 — canonical zero-register encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=16,vm=1,vs2=0,rs1=17,funct3=2,rd=0 → word=0x4208A057
val got = emit_vfirst_m(0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x08)
expect(got[3]) to_equal(0x42)
```

</details>

#### emit_vfirst_m rd=1 vs2=2 — non-zero GPR and vector source

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=16,vm=1,vs2=2,rs1=17,funct3=2,rd=1 → word=0x4228A0D7
val got = emit_vfirst_m(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x28)
expect(got[3]) to_equal(0x42)
```

</details>

### encode_rvv_misc — viota.m

#### emit_viota_m vd=0 vs2=0 — canonical zero-register encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=20,vm=1,vs2=0,vs1=16,funct3=2,vd=0 → word=0x52082057
val got = emit_viota_m(0, 0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x08)
expect(got[3]) to_equal(0x52)
```

</details>

#### emit_viota_m vd=1 vs2=2 — non-zero vector dest and source

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=20,vm=1,vs2=2,vs1=16,funct3=2,vd=1 → word=0x522820D7
val got = emit_viota_m(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x28)
expect(got[3]) to_equal(0x52)
```

</details>

### encode_rvv_misc — vid.v

#### emit_vid_v vd=0 — canonical zero-register encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=20,vm=1,vs2=0,vs1=17,funct3=2,vd=0 → word=0x5208A057
val got = emit_vid_v(0)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0x57)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x08)
expect(got[3]) to_equal(0x52)
```

</details>

#### emit_vid_v vd=1 — non-zero vector dest

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=20,vm=1,vs2=0,vs1=17,funct3=2,vd=1 → word=0x5208A0D7
val got = emit_vid_v(1)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x08)
expect(got[3]) to_equal(0x52)
```

</details>

### encode_rvv_misc — vcpop/vfirst funct6 collision sanity

#### vcpop.m and vfirst.m differ only in byte[1] (rs1 field)

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both use funct6=16; rs1=16 vs rs1=17 sits in bits[19:15] → byte[1]
# vcpop.m  rs1=16=10000: bit15=0 → byte[1] has bit7=0
# vfirst.m rs1=17=10001: bit15=1 → byte[1] has bit7=1
val cpop = emit_vcpop_m(1, 2)
val first = emit_vfirst_m(1, 2)
expect(cpop[0]) to_equal(first[0])
expect(cpop[2]) to_equal(first[2])
expect(cpop[3]) to_equal(first[3])
# byte[1] must differ: 0x20 vs 0xA0
expect(cpop[1]) to_equal(0x20)
expect(first[1]) to_equal(0xA0)
```

</details>

### encode_rvv_misc — viota/vid funct6 collision sanity

#### viota.m and vid.v share funct6=20 but differ in byte[1] (vs1 field)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# viota.m vs1=16=10000: bit15=0 → byte[1]=0x20
# vid.v   vs1=17=10001: bit15=1 → byte[1]=0xA0
val iota = emit_viota_m(1, 0)
val vid = emit_vid_v(1)
expect(iota[3]) to_equal(vid[3])
expect(iota[1]) to_equal(0x20)
expect(vid[1]) to_equal(0xA0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/rvv_misc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- encode_rvv_misc — vcpop.m
- encode_rvv_misc — vfirst.m
- encode_rvv_misc — viota.m
- encode_rvv_misc — vid.v
- encode_rvv_misc — vcpop/vfirst funct6 collision sanity
- encode_rvv_misc — viota/vid funct6 collision sanity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
