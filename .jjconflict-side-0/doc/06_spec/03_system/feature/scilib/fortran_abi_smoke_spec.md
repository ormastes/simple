# Fortran Abi Smoke Specification

> <details>

<!-- sdn-diagram:id=fortran_abi_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fortran_abi_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fortran_abi_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fortran_abi_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fortran Abi Smoke Specification

## Scenarios

### fortran_abi smoke

#### LP64 helpers return expected values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fortran_int_bytes()).to_equal(8)
expect(fortran_int_is_lp64()).to_equal(true)
```

</details>

#### index converters are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rc_to_rm_index(1, 2, 4)).to_equal(6)
expect(rc_to_cm_index(1, 2, 3)).to_equal(7)
```

</details>

#### symbol names are canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(blas_symbol_name("gemm", "d")).to_equal("rt_blas_dgemm")
expect(lapack_symbol_name("gesv")).to_equal("rt_lapack_dgesv")
expect(cuda_symbol_name("malloc")).to_equal("rt_cuda_malloc")
```

</details>

#### operand swap needed for row-major layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(operand_swap_needed(LAYOUT_ROW_MAJOR)).to_equal(true)
expect(operand_swap_needed(LAYOUT_COL_MAJOR)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/fortran_abi_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fortran_abi smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
