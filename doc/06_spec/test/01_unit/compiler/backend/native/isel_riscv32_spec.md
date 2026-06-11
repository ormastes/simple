# Isel Riscv32 Specification

> <details>

<!-- sdn-diagram:id=isel_riscv32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=isel_riscv32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

isel_riscv32_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=isel_riscv32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Isel Riscv32 Specification

## Scenarios

### Isel Riscv32

#### uses the shared ILP32D contract word size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.pointer_bits / 8).to_equal(4)
expect(contract.pointer_bits).to_equal(32)
expect(contract.stack_align_bytes).to_equal(16)
```

</details>

#### keeps RV32 Linux ABI metadata explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.abi_text()).to_equal("ilp32d")
expect(contract.arg_register_count).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/isel_riscv32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Isel Riscv32

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
