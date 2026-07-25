# Encode Rvv Float Specification

> <details>

<!-- sdn-diagram:id=encode_rvv_float_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_rvv_float_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_rvv_float_spec -> std
encode_rvv_float_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_rvv_float_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode Rvv Float Specification

## Scenarios

### RISC-V RVV floating-point encoders

#### encodes floating add, subtract, min, and max exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vfadd_vv(1, 2, 3)).to_equal([0xD7, 0x90, 0x21, 0x02])
expect(emit_vfsub_vv(1, 2, 3)).to_equal([0xD7, 0x90, 0x21, 0x0A])
expect(emit_vfmin_vv(1, 2, 3)).to_equal([0xD7, 0x90, 0x21, 0x12])
expect(emit_vfmax_vv(1, 2, 3)).to_equal([0xD7, 0x90, 0x21, 0x1A])
```

</details>

#### encodes floating multiply, divide, and fused ops exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(emit_vfmul_vv(1, 2, 3)).to_equal([0xD7, 0x90, 0x21, 0x92])
expect(emit_vfdiv_vv(1, 2, 3)).to_equal([0xD7, 0x90, 0x21, 0x82])
expect(emit_vfmadd_vv(1, 2, 3)).to_equal([0xD7, 0x10, 0x31, 0xA2])
expect(emit_vfmsub_vv(1, 2, 3)).to_equal([0xD7, 0x10, 0x31, 0xAA])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/encode_rvv_float_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V RVV floating-point encoders

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
