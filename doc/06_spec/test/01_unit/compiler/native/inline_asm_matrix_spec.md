# Inline Asm Matrix Specification

> Tests covering:

<!-- sdn-diagram:id=inline_asm_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inline_asm_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inline_asm_matrix_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inline_asm_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Asm Matrix Specification

## Scenarios

- uses braced raw asm for non-volatile instructions
- uses braced raw asm for volatile instructions
- keeps parenthesized syntax out of raw embedded asm fixtures
- covers x86_32 interpreter mode
- covers x86_32 loader mode
- covers x86_32 compiler mode
- covers x86_64 interpreter mode
- covers x86_64 loader mode
- covers x86_64 compiler mode
- covers arm32 interpreter mode
- covers arm32 loader mode
- covers arm32 compiler mode
- covers arm64 interpreter mode
- covers arm64 loader mode
- covers arm64 compiler mode
- covers riscv32 interpreter mode
- covers riscv32 loader mode
- covers riscv32 compiler mode
- covers riscv64 interpreter mode
- covers riscv64 loader mode
- covers riscv64 compiler mode
- documents interpreter as parse-and-skip only
- documents loader as preservation and linking
- documents compiler as raw instruction emission

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/inline_asm_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Inline asm canonical block syntax
- Inline asm x86_32 matrix
- Inline asm x86_64 matrix
- Inline asm arm32 matrix
- Inline asm arm64 matrix
- Inline asm riscv32 matrix
- Inline asm riscv64 matrix
- Inline asm mode contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
