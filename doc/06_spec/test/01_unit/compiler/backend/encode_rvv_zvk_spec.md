# Encode Rvv Zvk Specification

> <details>

<!-- sdn-diagram:id=encode_rvv_zvk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_rvv_zvk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_rvv_zvk_spec -> std
encode_rvv_zvk_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_rvv_zvk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode Rvv Zvk Specification

## Scenarios

### encode_rvv_zvk — Zvkned AES instructions

#### emit_vaesef_vv vd=1 vs2=2 — AES final-round enc

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x28,vm=1,vs2=2,vs1=0,vd=1 → word=0xA22020D7
val got = emit_vaesef_vv(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x20)
expect(got[3]) to_equal(0xA2)
```

</details>

#### emit_vaesem_vv vd=1 vs2=2 — AES middle-round enc

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x29,vm=1,vs2=2,vs1=0,vd=1 → word=0xA62020D7
val got = emit_vaesem_vv(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x20)
expect(got[3]) to_equal(0xA6)
```

</details>

#### emit_vaesdf_vv vd=1 vs2=2 — AES final-round dec

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2A,vm=1,vs2=2,vs1=0,vd=1 → word=0xAA2020D7
val got = emit_vaesdf_vv(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x20)
expect(got[3]) to_equal(0xAA)
```

</details>

#### emit_vaesdm_vv vd=1 vs2=2 — AES middle-round dec

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2B,vm=1,vs2=2,vs1=0,vd=1 → word=0xAE2020D7
val got = emit_vaesdm_vv(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x20)
expect(got[3]) to_equal(0xAE)
```

</details>

#### emit_vaeskf1_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd1

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x22,vm=1,vs2=2,vs1=2(uimm),vd=1 → word=0x8A2120D7
val got = emit_vaeskf1_vi(1, 2, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0x8A)
```

</details>

#### emit_vaeskf2_vi vd=1 vs2=2 uimm=2 — AES key schedule rnd2

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2A,vm=1,vs2=2,vs1=2(uimm),vd=1 → word=0xAA2120D7
# NOTE: same funct6 as vaesdf.vv but vs1=2 (nonzero) distinguishes in context
val got = emit_vaeskf2_vi(1, 2, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xAA)
```

</details>

#### emit_vaesz_vs vd=1 vs2=2 — AES round zero key

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2F,vm=1,vs2=2,vs1=0,vd=1 → word=0xBE2020D7
# NOTE: same funct6 as vsha2cl.vv but vs1=0 distinguishes in context
val got = emit_vaesz_vs(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x20)
expect(got[3]) to_equal(0xBE)
```

</details>

### encode_rvv_zvk — Zvknh SHA-2 instructions

#### emit_vsha2ms_vv vd=1 vs2=2 vs1=3 — SHA-2 msg schedule

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2D,vm=1,vs2=2,vs1=3,vd=1 → word=0xB621A0D7
val got = emit_vsha2ms_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xB6)
```

</details>

#### emit_vsha2ch_vv vd=1 vs2=2 vs1=3 — SHA-2 compress high

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2E,vm=1,vs2=2,vs1=3,vd=1 → word=0xBA21A0D7
val got = emit_vsha2ch_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xBA)
```

</details>

#### emit_vsha2cl_vv vd=1 vs2=2 vs1=3 — SHA-2 compress low

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2F,vm=1,vs2=2,vs1=3,vd=1 → word=0xBE21A0D7
# NOTE: same funct6 as vaesz.vs but vs1=3 (nonzero) distinguishes in context
val got = emit_vsha2cl_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xBE)
```

</details>

### encode_rvv_zvk — Zvkg GCM/GHASH instructions

#### emit_vghsh_vv vd=1 vs2=2 vs1=3 — GHASH multiply+acc

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x2C,vm=1,vs2=2,vs1=3,vd=1 → word=0xB221A0D7
val got = emit_vghsh_vv(1, 2, 3)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0xA0)
expect(got[2]) to_equal(0x21)
expect(got[3]) to_equal(0xB2)
```

</details>

#### emit_vgmul_vv vd=1 vs2=2 — GHASH multiply

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# funct6=0x29,vm=1,vs2=2,vs1=0,vd=1 → word=0xA62020D7
# NOTE: same funct6 as vaesem.vv but vs1=0 distinguishes in context
val got = emit_vgmul_vv(1, 2)
expect(got.length) to_equal(4)
expect(got[0]) to_equal(0xD7)
expect(got[1]) to_equal(0x20)
expect(got[2]) to_equal(0x20)
expect(got[3]) to_equal(0xA6)
```

</details>

### encode_rvv_zvk — collision sanity checks

#### vaesz_vs and vsha2cl_vv differ in byte[2] (vs1 field)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both use funct6=0x2F; vs1 is in bits[19:15] -> byte[2]
# vaesz.vs  vs1=0: byte[2]=0x20
# vsha2cl.vv vs1=3: byte[2]=0xA0 (3 * 2^15 / 2^16 contributes to byte[2])
val aesz = emit_vaesz_vs(1, 2)
val sha2cl = emit_vsha2cl_vv(1, 2, 3)
# vaesz_vs word=0xBE2020D7 → byte[2]=0x20
expect(aesz[2]) to_equal(0x20)
# vsha2cl_vv word=0xBE21A0D7 → byte[2]=0xA0 (vs1=3 adds to bits[19:15])
expect(sha2cl[2]) to_equal(0xA0)
```

</details>

#### vaesem_vv and vgmul_vv produce same bytes when vs1=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both use funct6=0x29, vm=1, vs1=0; encoding is identical
# This is by spec design — disambiguated by ISA extension context
val aesem = emit_vaesem_vv(1, 2)
val vgmul = emit_vgmul_vv(1, 2)
expect(aesem[0]) to_equal(vgmul[0])
expect(aesem[1]) to_equal(vgmul[1])
expect(aesem[2]) to_equal(vgmul[2])
expect(aesem[3]) to_equal(vgmul[3])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/encode_rvv_zvk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- encode_rvv_zvk — Zvkned AES instructions
- encode_rvv_zvk — Zvknh SHA-2 instructions
- encode_rvv_zvk — Zvkg GCM/GHASH instructions
- encode_rvv_zvk — collision sanity checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
