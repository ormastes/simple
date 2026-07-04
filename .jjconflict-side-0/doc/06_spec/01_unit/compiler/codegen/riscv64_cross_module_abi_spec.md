# Riscv64 Cross Module Abi Specification

> <details>

<!-- sdn-diagram:id=riscv64_cross_module_abi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_cross_module_abi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_cross_module_abi_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_cross_module_abi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Cross Module Abi Specification

## Scenarios

### riscv64 cross-module ABI contracts

#### pointer width — LP64 vs ILP32

#### riscv64-linux preset has 64-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_riscv64_linux()
expect(preset.pointer_width).to_equal(64)
```

</details>

#### riscv32-baremetal preset has 32-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Contrast: cross-module pointer loads on rv32 must NOT be widened
# to 64 bits or the value is corrupted.
val preset = preset_riscv32_baremetal()
expect(preset.pointer_width).to_equal(32)
```

</details>

#### riscv64 and riscv32 pointer widths differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64 = preset_riscv64_linux()
val rv32 = preset_riscv32_baremetal()
expect(rv64.pointer_width == rv32.pointer_width).to_equal(false)
```

</details>

#### ABI — LP64D

#### riscv64-linux preset ABI is lp64d

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_riscv64_linux()
expect(preset.abi).to_equal("lp64d")
```

</details>

#### riscv64 contract pointer_bits is 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.pointer_bits).to_equal(64)
```

</details>

#### riscv64 contract has 8 argument registers (a0-a7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.arg_register_count).to_equal(8)
```

</details>

#### riscv64 contract stack alignment is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.stack_align_bytes).to_equal(16)
```

</details>

#### riscv64 ABI text is lp64d or lp64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
val abi = contract.abi_text()
val is_lp64d = abi == "lp64d"
val is_lp64 = abi == "lp64"
expect(is_lp64d or is_lp64).to_equal(true)
```

</details>

#### architecture triple

#### riscv64-linux triple starts with riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
val triple = contract.triple()
expect(triple.starts_with("riscv64")).to_equal(true)
```

</details>

#### riscv64-linux triple contains linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
val triple = contract.triple()
expect(triple.contains("linux")).to_equal(true)
```

</details>

#### module-level val safety (non-baremetal)

#### riscv64-linux is NOT a baremetal preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# baremetal_module_val_zero bug only affects --target *-unknown-none.
# riscv64-linux is an OS-hosted target: ELF loader initialises BSS,
# so module-level val constants are NOT zero at startup.
val preset = preset_riscv64_linux()
expect(preset_is_baremetal(preset)).to_equal(false)
```

</details>

#### riscv64-linux has no_std=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_riscv64_linux()
expect(preset.no_std).to_equal(false)
```

</details>

#### riscv64-linux has float support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_riscv64_linux()
expect(preset.float_support).to_equal(true)
```

</details>

#### cross-module symbol mangling

#### riscv64 contract arch field is riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The arch field drives the triple component used in mangled symbol
# names for rv64 cross-module imports. Must be "riscv64" (not "rv64"
# or "riscv64gc") so linker symbol resolution is deterministic.
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.arch).to_equal("riscv64")
```

</details>

#### riscv64 contract os field is linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.os).to_equal("linux")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/riscv64_cross_module_abi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- riscv64 cross-module ABI contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
