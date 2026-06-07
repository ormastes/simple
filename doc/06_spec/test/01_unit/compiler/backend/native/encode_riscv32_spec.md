# Encode Riscv32 Specification

> <details>

<!-- sdn-diagram:id=encode_riscv32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=encode_riscv32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

encode_riscv32_spec -> std
encode_riscv32_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=encode_riscv32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Encode Riscv32 Specification

## Scenarios

### Encode Riscv32

#### retains ELF32 constants for the RV32 Linux lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ELF32_EI_CLASS).to_equal(1)
expect(ELF32_HEADER_SIZE).to_equal(52)
```

</details>

#### shares the Linux call relocation and ABI contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.call_plt_reloc).to_equal(19)
expect(contract.abi_text()).to_equal("ilp32d")
expect(contract.march).to_equal("rv32gc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/encode_riscv32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Encode Riscv32

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
