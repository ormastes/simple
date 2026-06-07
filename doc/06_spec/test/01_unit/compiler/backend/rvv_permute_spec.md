# Rvv Permute Specification

> <details>

<!-- sdn-diagram:id=rvv_permute_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rvv_permute_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rvv_permute_spec -> std
rvv_permute_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rvv_permute_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Permute Specification

## Scenarios

### RVV vslideup/vslidedown byte-level emit

#### vslideup.vx v0, v0, x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_list_hex(emit_rvv_vslideup_vx(0, 0, 0))).to_equal("5740003a")
```

</details>

#### vslidedown.vx v0, v0, x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_list_hex(emit_rvv_vslidedown_vx(0, 0, 0))).to_equal("5740003e")
```

</details>

#### vslide1up.vx v0, v0, x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_list_hex(emit_rvv_vslide1up_vx(0, 0, 0))).to_equal("5760003a")
```

</details>

#### vslide1down.vx v0, v0, x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_list_hex(emit_rvv_vslide1down_vx(0, 0, 0))).to_equal("5760003e")
```

</details>

#### vslideup.vx v1, v2, x3 (non-zero regs)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_list_hex(emit_rvv_vslideup_vx(1, 2, 3))).to_equal("d7c0213a")
```

</details>

### RVV vrgather byte-level emit

#### vrgather.vv v0, v0, v0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_list_hex(emit_rvv_vrgather_vv(0, 0, 0))).to_equal("57000032")
```

</details>

#### vrgather.vx v0, v0, x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_list_hex(emit_rvv_vrgather_vx(0, 0, 0))).to_equal("57400032")
```

</details>

#### vrgather.vv vs vrgather.vx differ in byte[1] (funct3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vv = emit_rvv_vrgather_vv(0, 0, 0)
val vx = emit_rvv_vrgather_vx(0, 0, 0)
expect(vv[1] == vx[1]).to_equal(false)
```

</details>

### RVV permute output properties

#### all outputs are 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_rvv_vslideup_vx(0, 0, 0).len()).to_equal(4)
expect(emit_rvv_vrgather_vv(0, 0, 0).len()).to_equal(4)
```

</details>

#### slideup vs slidedown differ only in byte[3] high bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val up = emit_rvv_vslideup_vx(0, 0, 0)
val dn = emit_rvv_vslidedown_vx(0, 0, 0)
expect(up[0] == dn[0]).to_equal(true)
expect(up[3] == dn[3]).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/rvv_permute_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RVV vslideup/vslidedown byte-level emit
- RVV vrgather byte-level emit
- RVV permute output properties

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
