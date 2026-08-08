# Isel X86 64 Specification

> <details>

<!-- sdn-diagram:id=isel_x86_64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=isel_x86_64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

isel_x86_64_spec -> std
isel_x86_64_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=isel_x86_64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Isel X86 64 Specification

## Scenarios

### Isel X86_64 rotate intrinsic lowering

#### lowers bit_rotate_left into shift-or machine ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mach = isel_module(build_rotate_module("rol_test", "bit_rotate_left"))
val block = entry_block(mach)

expect(rotate_window(block)).to_equal([
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_IMM,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_SHL,
    X86_OP_MOV_REG_IMM,
    X86_OP_SUB,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_SHR,
    X86_OP_OR
])
```

</details>

#### lowers bit_rotate_right into mirrored shift-or machine ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mach = isel_module(build_rotate_module("ror_test", "bit_rotate_right"))
val block = entry_block(mach)

expect(rotate_window(block)).to_equal([
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_IMM,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_MOV_REG_REG,
    X86_OP_SHR,
    X86_OP_MOV_REG_IMM,
    X86_OP_SUB,
    X86_OP_AND,
    X86_OP_MOV_REG_REG,
    X86_OP_SHL,
    X86_OP_OR
])
```

</details>

### Isel X86_64 bit_bswap intrinsic lowering

#### lowers bit_bswap into move plus bswap

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mach = isel_module(build_bswap_module("bswap_test"))
val block = entry_block(mach)
val bswap_idx = find_opcode(block, X86_OP_BSWAP)
expect(bswap_idx >= 0).to_equal(true)
expect(opcode_at(block, bswap_idx - 1)).to_equal(X86_OP_MOV_REG_REG)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/isel_x86_64_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Isel X86_64 rotate intrinsic lowering
- Isel X86_64 bit_bswap intrinsic lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
