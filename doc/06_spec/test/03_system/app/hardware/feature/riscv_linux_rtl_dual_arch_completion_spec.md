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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Linux Rtl Dual Arch Completion Specification

## Scenarios

### REQ-RLD-001..006

#### keeps dual-arch QEMU virt profiles public and deterministic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RiscvPlatformProfile.qemu_virt_rv32().name).to_equal("qemu_virt_rv32")
expect(RiscvPlatformProfile.qemu_virt_rv64().name).to_equal("qemu_virt_rv64")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-RLD-001..006

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
