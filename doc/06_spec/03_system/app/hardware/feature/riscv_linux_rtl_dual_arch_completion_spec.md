# Riscv Linux Rtl Dual Arch Completion Specification

> <details>

<!-- sdn-diagram:id=riscv_linux_rtl_dual_arch_completion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_linux_rtl_dual_arch_completion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_linux_rtl_dual_arch_completion_spec -> std
riscv_linux_rtl_dual_arch_completion_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_linux_rtl_dual_arch_completion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Linux Rtl Dual Arch Completion Specification

## Scenarios

### REQ-RLD-001..007

#### keeps dual-arch QEMU virt profiles public and deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_virt_rv32_platform_profile().name).to_equal("qemu_virt_rv32")
expect(qemu_virt_rv64_platform_profile().name).to_equal("qemu_virt_rv64")
```

</details>

#### keeps the default FPGA manifest dual-arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = create_default_riscv_fpga_linux_manifest()
expect(manifest.lanes.len()).to_equal(2)
expect(manifest.readiness_summary()).to_contain("rv32:")
expect(manifest.readiness_summary()).to_contain("rv64:")
```

</details>

#### publishes product configuration, budget, and formal gates per lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = create_default_riscv_fpga_linux_manifest()
val text = manifest.rtl_manifest_text("/tmp/riscv_linux_rtl_dual_arch_completion")
expect(text).to_contain("product_level = \"linux-rtl\"")
expect(text).to_contain("configuration_profile = \"qemu-virt+fpga-board\"")
expect(text).to_contain("linux_abi = \"ilp32d\"")
expect(text).to_contain("linux_abi = \"lp64d\"")
expect(text).to_contain("linux_mmu = \"sv32\"")
expect(text).to_contain("linux_mmu = \"sv39\"")
expect(text).to_contain("rtl_size_budget_luts = \"25000\"")
expect(text).to_contain("rtl_size_budget_luts = \"45000\"")
expect(text).to_contain("perf_target_mhz = \"50\"")
expect(text).to_contain("formal_verification = \"rvfi+sby\"")
expect(text).to_contain("formal_gate = \"rvfi_port_manifest\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl` |
| Updated | 2026-07-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-RLD-001..007

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
