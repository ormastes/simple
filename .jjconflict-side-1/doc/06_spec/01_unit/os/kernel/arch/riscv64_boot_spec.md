# Riscv64 Boot Specification

> 1. Rv64Boot save boot args

<!-- sdn-diagram:id=riscv64_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_boot_spec -> std
riscv64_boot_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Boot Specification

## Scenarios

### rv64 boot bootstrap trap runtime

#### records boot arguments

1. Rv64Boot save boot args
   - Expected: Rv64Boot.hart_id() equals `3`
   - Expected: Rv64Boot.dtb_address() equals `0x88000000`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Rv64Boot.save_boot_args(3, 0x88000000)
expect(Rv64Boot.hart_id()).to_equal(3)
expect(Rv64Boot.dtb_address()).to_equal(0x88000000)
```

</details>

#### keeps boot argument capture independent from trap runtime setup

1. Rv64Boot save boot args
   - Expected: Rv64Boot.hart_id() equals `0`
   - Expected: Rv64Boot.dtb_address() equals `0x87000000`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Rv64Boot.save_boot_args(0, 0x87000000)
expect(Rv64Boot.hart_id()).to_equal(0)
expect(Rv64Boot.dtb_address()).to_equal(0x87000000)
```

</details>

#### keeps the fixed kernel load address

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Rv64Boot.kernel_load_address()).to_equal(0x80200000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rv64 boot bootstrap trap runtime

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
